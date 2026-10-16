"""One-GPU public pinning campaign with durable intents and independent CPU checks.

No resource provisioning, signing or broadcasting. Runs only an already approved
binary in an isolated runtime. Every uncertain/failed range blocks resumption.
"""
import argparse
import base64
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'worker'))
from search_ranges import work_range
from candidate_range import validate_candidates_in_range
VERSION='qsb-config-a-cmsverify-v1'
CPU_FILES={'handler.py','bitcoin_tx.py','qsb_pipeline.py','secp256k1.py','verify_hit.py','gpu_emulator.py'}


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def canonical(value): return json.dumps(value,sort_keys=True,separators=(',',':'))

def save(path,value):
    temporary=path.with_suffix(path.suffix+'.tmp')
    with temporary.open('w') as stream:
        json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
    temporary.replace(path)
    fd=os.open(path.parent,os.O_RDONLY)
    try:os.fsync(fd)
    finally:os.close(fd)


def cpu(reference,event):
    # A fresh isolated interpreter avoids the reference's temporary cwd mutation.
    program='import sys,json;sys.path.insert(0,sys.argv[1]);from handler import handler;print(json.dumps(handler(json.load(sys.stdin))))'
    result=subprocess.run([sys.executable,'-I','-c',program,str(reference)],input=json.dumps(event),
                          capture_output=True,text=True,timeout=60,env={'PATH':os.environ.get('PATH',''),'PYTHONDONTWRITEBYTECODE':'1'})
    if result.returncode:raise ValueError('Independent CPU reference failed: '+result.stderr[-2000:])
    return json.loads(result.stdout)


def verify_artifacts(binary,binary_hash,reference,source_hashes):
    if not re.fullmatch('[0-9a-f]{64}',binary_hash) or sha(binary)!=binary_hash:
        raise ValueError('Binary mismatch')
    if set(source_hashes)!=CPU_FILES:raise ValueError('CPU source inventory mismatch')
    if {p.name for p in reference.glob('*.py')} != CPU_FILES:raise ValueError('Unexpected CPU modules')
    for name,digest in source_hashes.items():
        if sha(reference/name)!=digest:raise ValueError('CPU source mismatch: '+name)


def verify_public(public,reference):
    if set(public)!={'request','export'}:raise ValueError('Unexpected public envelope fields')
    event=public['request']
    if set(event)!={'action','scriptVersion','publicStateJson','manifest','stage'} or event['stage']!='pinning' or event['action']!='export' or event['scriptVersion']!=VERSION:
        raise ValueError('Corrected public pinning request required')
    exported=cpu(reference,event)
    if exported!=public['export']:raise ValueError('Independent CPU export mismatch')
    raw=base64.b64decode(exported['parameterBase64'],validate=True)
    if hashlib.sha256(raw).hexdigest()!=exported['parameterSha256']:raise ValueError('Parameter hash mismatch')
    return raw


def resume_status(root,binding):
    records=[]
    for path in sorted(root.glob('range-*/record.json')):
        record=json.loads(path.read_text())
        if record['binding']!=binding:raise ValueError('Range binding changed')
        if record['workRange']!=work_range('pinning',record['attempt']):raise ValueError('Range partition changed')
        if record['status'] in ('complete','verified-hit') and sha(path.parent/'result.json')!=record.get('resultSha256'):
            raise ValueError('Completed result missing or changed')
        records.append(record)
    records.sort(key=lambda r:r['attempt'])
    for attempt,record in enumerate(records):
        if record['attempt']!=attempt:raise ValueError('Coverage gap')
        if record['status']=='verified-hit':return attempt,record['solution']
        if record['status']!='complete':raise ValueError('Failed or uncertain range requires reconciliation; no resubmission')
    # A crashed directory creation or intent write also blocks instead of retrying.
    if len(list(root.glob('range-*')))!=len(records):raise ValueError('Incomplete range directory; reconcile')
    return len(records),None


def compute(binary,raw,unit,directory,timeout):
    (directory/'params.bin').write_bytes(raw)
    command=[str(binary),'params.bin','0','1','0','single_hash',f"seq_start={unit['sequence']}",
             f"seq_count={unit['sequenceCount']}",f"lt_start={unit['locktime']}",f"lt_count={unit['count']//unit['sequenceCount']}"]
    started=time.monotonic()
    with (directory/'compute.log').open('w') as output:
        process=subprocess.Popen(command,cwd=directory,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,
                                 env={'PATH':os.environ.get('PATH',''),'HOME':'/tmp'})
        try:process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGTERM)
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait()
            raise TimeoutError('Range timed out; preserved partial logs; no automatic retry')
        finally:output.flush();os.fsync(output.fileno())
    log=(directory/'compute.log').read_text()
    if process.returncode!=0 or 'Done:' not in log or 'QSB_RANGE_INCOMPLETE' in log:
        raise ValueError('Range failed or completion absent')
    hits=[]
    for path in sorted((directory/'results').glob('*hit*.txt')):
        if path.stat().st_size>=16384 or len(hits)>=32:raise ValueError('Hit capacity exceeded')
        hits.append(path.read_text())
    return {'elapsedSeconds':time.monotonic()-started,'logSha256':sha(directory/'compute.log'),'candidates':hits}


def checked_solution(public,candidates,unit,verify):
    validate_candidates_in_range('pinning',candidates,unit)
    solutions=[]
    for candidate in candidates:
        for record in [r for r in re.split(r'(?=^sequence=)',candidate,flags=re.M) if r.strip()]:
            verdict=verify({**public['request'],'action':'verify','candidates':[record]})
            fields=dict(re.findall(r'^([a-z_]+)=([^\n]+)$',record,re.M))
            expected={'sequence':int(fields['sequence']),'locktime':int(fields['locktime'])}
            if verdict.get('scriptVersion')!=VERSION or verdict.get('valid') is not True or any(verdict.get(k)!=v for k,v in expected.items()):
                raise ValueError('Independent CPU rejected candidate')
            solutions.append(expected)
    return solutions[0] if solutions else None


def run(args):
    root=args.output.resolve();root.mkdir(parents=True,exist_ok=True)
    lock=(root/'.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    binary=args.binary.resolve();reference=args.reference.resolve()
    sources=json.loads(args.reference_hashes.read_text());public=json.loads(args.public.read_text())
    verify_artifacts(binary,args.binary_sha256,reference,sources)
    raw=verify_public(public,reference)
    gpu=subprocess.check_output(['nvidia-smi','--query-gpu=uuid','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines())!=1 or not gpu:raise ValueError('Exactly one GPU required')
    identity={'publicSha256':hashlib.sha256(canonical(public).encode()).hexdigest(),'binarySha256':args.binary_sha256,
              'referenceHashes':sources,'scriptVersion':VERSION,'searchVersion':'ranked-v2','deadline':args.deadline,
              'rangeTimeout':args.range_timeout}
    binding=hashlib.sha256(canonical(identity).encode()).hexdigest()
    campaign=root/'campaign.json'
    if campaign.exists():
        if json.loads(campaign.read_text())['identity']!=identity:raise ValueError('Campaign identity changed')
    else:
        if any(p.name!='.lock' for p in root.iterdir()):raise ValueError('New empty campaign directory required')
        if not 0<args.deadline-time.time()<=23*3600:raise ValueError('Deadline must be within23hours')
        save(campaign,{'identity':identity,'binding':binding,'createdAt':time.time(),'gpu':gpu})
    attempt,solution=resume_status(root,binding)
    if solution:return {'status':'verified-hit','solution':solution}
    while args.deadline-time.time()>args.range_timeout+90:
        verify_artifacts(binary,args.binary_sha256,reference,sources)
        unit=work_range('pinning',attempt)
        directory=root/f'range-{attempt:08d}';directory.mkdir()
        record={'status':'compute-intent','binding':binding,'attempt':attempt,'workRange':unit,'startedAt':time.time()}
        save(directory/'record.json',record)  # Persist before any GPU process.
        try:
            result=compute(binary,raw,unit,directory,args.range_timeout)
            save(directory/'result.json',result)
            solution=checked_solution(public,result['candidates'],unit,lambda event:cpu(reference,event))
            record.update(status='verified-hit' if solution else 'complete',resultSha256=sha(directory/'result.json'),finishedAt=time.time())
            if solution:record['solution']=solution
            save(directory/'record.json',record)
            if solution:
                save(root/'solution.json',solution)
                return {'status':'verified-hit','solution':solution,'attempt':attempt}
        except BaseException as exc:
            record.update(status='failed',error=str(exc),finishedAt=time.time());save(directory/'record.json',record)
            raise
        attempt+=1
    return {'status':'deadline-stop','nextAttempt':attempt,'binding':binding}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('public','binary','reference','reference-hashes','output'):parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--binary-sha256',required=True)
    parser.add_argument('--deadline',type=int,required=True)
    parser.add_argument('--range-timeout',type=int,default=840)
    args=parser.parse_args()
    if not 1<=args.range_timeout<=840:parser.error('range timeout must be1..840seconds')
    print(json.dumps(run(args)))

if __name__=='__main__':main()
