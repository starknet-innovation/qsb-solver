"""Public-only stage advancement and one-shot corrected subset range execution.

Uses the same external intent acknowledgement as fresh_pinning_search. No cloud
calls, signing, relaxed predicates, or automatic uncertain-range retries.
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
import time

import fresh_pinning_search as common
from search_ranges import work_range, SUBSET_TOTAL, CHUNK


def require_pin(public, solution, verify):
    expected={'sequence','locktime'}
    if not expected <= set(solution) or any(type(solution[k]) is not int for k in expected):
        raise ValueError('Integer public pin required')
    record=f"sequence={solution['sequence']}\nlocktime={solution['locktime']}"
    verdict=verify({**public['request'],'action':'verify','candidates':[record]})
    if verdict.get('scriptVersion')!=common.VERSION or verdict.get('valid') is not True or any(verdict.get(k)!=solution[k] for k in expected):
        raise ValueError('CPU rejected pin')


def indices_record(values):
    if not isinstance(values,list) or len(values)!=9 or any(type(v) is not int or not 0<=v<150 for v in values) or len(set(values))!=9:
        raise ValueError('Nine distinct CPU/HORS indices required')
    return 'indices='+','.join(map(str,sorted(149-v for v in values)))


def stage_event(public,solution,stage):
    return {**public['request'],'stage':stage,'sequence':solution['sequence'],'locktime':solution['locktime']}


def export_stage(public,solution,stage,verify):
    if stage not in ('round1','round2') or set(solution)!=({'sequence','locktime'} if stage=='round1' else {'sequence','locktime','round1'}):
        raise ValueError('Exact previous-stage public solution required')
    require_pin(public,solution,verify)
    if stage=='round2':
        verdict=verify({**stage_event(public,solution,'round1'),'action':'verify','candidates':[indices_record(solution['round1'])]})
        if verdict.get('scriptVersion')!=common.VERSION or verdict.get('valid') is not True or verdict.get('indices')!=sorted(solution['round1']):
            raise ValueError('CPU rejected prior round 1')
    event=stage_event(public,solution,stage)
    exported=verify(event)
    if exported.get('scriptVersion')!=common.VERSION:
        raise ValueError('Export version mismatch')
    raw=base64.b64decode(exported['parameterBase64'],validate=True)
    if hashlib.sha256(raw).hexdigest()!=exported['parameterSha256']:
        raise ValueError('Export parameter mismatch')
    return event,exported,raw


def checked_solution(event,prior,candidates,unit,verify):
    stage=event['stage'];common.validate_candidates_in_range(stage,candidates,unit)
    hits=[]
    for candidate in candidates:
        for record in [r for r in re.split(r'(?=^indices=)',candidate,flags=re.M) if r.strip()]:
            fields=dict(re.findall(r'^([a-z_]+)=([^\n]+)$',record,re.M))
            expected=sorted(149-int(i) for i in fields['indices'].split(','))
            verdict=verify({**event,'action':'verify','candidates':[record]})
            if verdict.get('scriptVersion')!=common.VERSION or verdict.get('valid') is not True or verdict.get('indices')!=expected:
                raise ValueError('Independent CPU rejected subset candidate')
            hits.append({**prior,stage:expected})
    return hits[0] if hits else None


def resume(root,binding,stage):
    paths=sorted(root.glob('range-*/record.json'))
    if len(paths)!=len(list(root.glob('range-*'))):raise ValueError('Incomplete range directory; reconcile')
    hit=None
    for attempt,path in enumerate(paths):
        record=json.loads(path.read_text())
        if hit is not None or record['attempt']!=attempt or record['binding']!=binding or record['workRange']!=work_range(stage,attempt):
            raise ValueError('Coverage gap, overlap or binding mismatch')
        if record['status'] not in ('complete','verified-hit'):
            raise ValueError('Uncertain or failed range; no resubmission')
        if common.sha(path.parent/'result.json')!=record['resultSha256']:
            raise ValueError('Result changed')
        result=json.loads((path.parent/'result.json').read_text())
        if common.sha(path.parent/'compute.log')!=result['logSha256']:
            raise ValueError('Log changed')
        if record['status']=='verified-hit':hit=record['solution']
    return len(paths),hit


def compute(binary,raw,unit,directory,timeout,solution):
    (directory/'params.bin').write_bytes(raw)
    command=[str(binary),'params.bin','0',str(solution['sequence']),str(solution['locktime']),'1','0','single_hash',
             f"rank_start={unit['start']}",f"rank_count={unit['count']}"]
    started=time.monotonic()
    with (directory/'compute.log').open('w') as output:
        process=subprocess.Popen(command,cwd=directory,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,
                                 env={'PATH':os.environ.get('PATH',''),'HOME':'/tmp'})
        try:
            while process.poll() is None:
                if (directory/'compute.log').stat().st_size>common.MAX_LOG:raise OverflowError('Log capacity exceeded')
                remaining=timeout-(time.monotonic()-started)
                if remaining<=0:raise subprocess.TimeoutExpired(command,timeout)
                try:process.wait(timeout=min(.2,remaining))
                except subprocess.TimeoutExpired:pass
        except BaseException:
            if process.poll() is None:
                os.killpg(process.pid,signal.SIGTERM)
                try:process.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait()
            raise
        finally:output.flush();os.fsync(output.fileno())
    if (directory/'compute.log').stat().st_size>common.MAX_LOG:raise ValueError('Log capacity exceeded')
    log=(directory/'compute.log').read_text()
    if process.returncode!=0 or 'Done enum:' not in log or 'QSB_RANGE_INCOMPLETE' in log:
        raise ValueError('Subset failed or incomplete')
    hits=[]
    for path in sorted((directory/'results').glob('*hit*.txt')):
        if path.stat().st_size>=16384 or len(hits)>=32:raise ValueError('Hit capacity exceeded')
        hits.append(path.read_text())
    return {'elapsedSeconds':time.monotonic()-started,'logSha256':common.sha(directory/'compute.log'),'candidates':hits}


def run(args):
    root=args.output.resolve();root.mkdir(parents=True,exist_ok=True)
    with (root/'.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        binary=args.binary.resolve();reference=args.reference.resolve()
        public=json.loads(args.public.read_text());prior=json.loads(args.solution.read_text())
        sources=json.loads(args.reference_hashes.read_text())
        common.verify_artifacts(binary,args.binary_sha256,reference,sources)
        common.verify_public(public,reference)
        event,exported,raw=export_stage(public,prior,args.stage,lambda e:common.cpu(reference,e))
        gpu=subprocess.check_output(['nvidia-smi','--query-gpu=uuid','--format=csv,noheader'],text=True).strip()
        if len(gpu.splitlines())!=1 or not gpu:raise ValueError('Exactly one GPU required')
        identity={'stage':args.stage,'publicSha256':hashlib.sha256(common.canonical(public).encode()).hexdigest(),
                  'solution':prior,'parameterSha256':exported['parameterSha256'],'binarySha256':args.binary_sha256,
                  'referenceHashes':sources,'scriptVersion':common.VERSION,'searchVersion':'ranked-v2',
                  'deadline':args.deadline,'rangeTimeout':args.range_timeout}
        binding=hashlib.sha256(common.canonical(identity).encode()).hexdigest()
        campaign=root/'campaign.json'
        if campaign.exists():
            if json.loads(campaign.read_text())['identity']!=identity:raise ValueError('Campaign identity changed')
        else:
            if any(p.name!='.lock' for p in root.iterdir()):raise ValueError('Fresh stage directory required')
            if not 0<args.deadline-time.time()<=23*3600:raise ValueError('Deadline must be within 23 hours')
            common.save(campaign,{'identity':identity,'binding':binding,'createdAt':time.time(),'gpu':gpu})
            common.save(root/'public-export.json',{'request':event,'export':exported})
        if args.mode=='prepare':
            attempt,hit=resume(root,binding,args.stage)
            if hit:return {'status':'verified-hit','solution':hit,'binding':binding}
            if args.deadline-time.time()<=args.range_timeout+90:return {'status':'deadline-stop','nextAttempt':attempt,'binding':binding}
            if attempt*CHUNK>=SUBSET_TOTAL:return {'status':'exhausted','nextAttempt':attempt,'binding':binding}
            if sum(p.stat().st_size for p in root.rglob('*') if p.is_file())>common.MAX_SNAPSHOT-2*common.MAX_LOG:
                return {'status':'snapshot-capacity-stop','nextAttempt':attempt,'binding':binding}
            directory=root/f'range-{attempt:08d}';directory.mkdir()
            common.save(directory/'record.json',{'status':'prepared','binding':binding,'attempt':attempt,'workRange':work_range(args.stage,attempt),'preparedAt':time.time()})
            return {'status':'prepared','attempt':attempt,'binding':binding}
        attempt=args.attempt
        if type(attempt) is not int or attempt<0:raise ValueError('Execute requires prepared attempt')
        directory=root/f'range-{attempt:08d}';path=directory/'record.json'
        record=json.loads(path.read_text());unit=work_range(args.stage,attempt)
        if record['status']!='prepared' or record['binding']!=binding or record['attempt']!=attempt or record['workRange']!=unit:
            raise ValueError('Not exact unexecuted intent; reconcile')
        if args.deadline-time.time()<=args.range_timeout+90:raise ValueError('Insufficient time')
        record.update(status='compute-intent',startedAt=time.time());common.save(path,record)
        try:
            common.await_intent_ack(path,args.intent_ack_dir,binding,attempt)
            result=compute(binary,raw,unit,directory,args.range_timeout,prior);common.save(directory/'result.json',result)
            hit=checked_solution(event,prior,result['candidates'],unit,lambda e:common.cpu(reference,e))
            record.update(status='verified-hit' if hit else 'complete',resultSha256=common.sha(directory/'result.json'),finishedAt=time.time())
            if hit:record['solution']=hit
            common.save(path,record)
            if hit:common.save(root/'solution.json',hit)
            return {'status':record['status'],'solution':hit,'attempt':attempt,'binding':binding}
        except BaseException as exc:
            record.update(status='failed',error=str(exc),finishedAt=time.time());common.save(path,record);raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['prepare','execute']);parser.add_argument('--attempt',type=int)
    parser.add_argument('--stage',choices=['round1','round2'],required=True)
    for name in ('public','solution','binary','reference','reference-hashes','output','intent-ack-dir'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--binary-sha256',required=True);parser.add_argument('--deadline',type=int,required=True)
    parser.add_argument('--range-timeout',type=int,default=840)
    args=parser.parse_args()
    if not 1<=args.range_timeout<=840:parser.error('range timeout must be 1..840 seconds')
    print(json.dumps(run(args)))

if __name__=='__main__':main()
