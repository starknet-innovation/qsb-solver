"""Matched sm86 subset timing. Public synthetic fixtures; no range credit."""
import base64
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from run_a10g import validate_binding, SUB

BASELINE = '672cf6689fd6e0c71d992ab2a6df2687ac9b2b0d5c7de42d63db6b51b69c6b5d'
COUNT = 1 << 29
FULL_RANGE = 1 << 34
NAMES = {'wpkh-round1','wpkh-round2','taproot-round1','taproot-round2'}


def check_sample(row):
    if row['count'] != COUNT or row['rank'] != 0:
        raise ValueError('wrong sample range')
    seconds=row['seconds']
    if type(seconds) not in (int,float) or not math.isfinite(seconds) or not 0 < seconds <= 120:
        raise ValueError('invalid timing')
    if row.get('timedOut',False) is not False or row['exit'] != 0 or 'QSB_RANGE_INCOMPLETE' in row['log']:
        raise ValueError('failed sample')
    if len(re.findall(r'\[GPU 0\] Done enum:',row['log'])) != 1:
        raise ValueError('missing unique completion')
    statuses=re.findall(r'^STATUS=.*$',row['summary'],re.M)
    if len(statuses)!=1 or not re.fullmatch(r'STATUS=EXHAUSTED \d+ total_attempts='+str(COUNT)+r' elapsed_s=\d+ hits=0',statuses[0]):
        raise ValueError('incomplete or shortened sample')
    if row['hitFiles'] or re.search(r'^HIT ',row['summary'],re.M):
        raise ValueError('unexpected hit requires CPU review')


class SampleFailure(RuntimeError):
    def __init__(self, row):
        super().__init__('sample failed; diagnostics retained')
        self.row=row


def execute(binary, fixture, deadline):
    remaining=min(120,deadline-time.monotonic())
    if remaining<=0:raise TimeoutError('benchmark deadline')
    with tempfile.TemporaryDirectory() as directory:
        root=Path(directory);(root/'params.bin').write_bytes(base64.b64decode(fixture['params'],validate=True))
        command=[str(binary),'params.bin','0',str(fixture['sequence']),str(fixture['locktime']),
                 '1','0','single_hash','rank_start=0',f'rank_count={COUNT}']
        started=time.monotonic()
        process=subprocess.Popen(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
        timed_out=False
        try:output,_=process.communicate(timeout=remaining)
        except subprocess.TimeoutExpired:
            timed_out=True
            try:os.killpg(process.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            output,_=process.communicate()
        except BaseException:
            try:os.killpg(process.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            process.communicate();raise
        seconds=time.monotonic()-started
        summary=root/'results/digest_summary_gpu0.txt'
        row=dict(count=COUNT,rank=0,seconds=seconds,exit=process.returncode,timedOut=timed_out,
                 log=output.decode(errors='replace'),summary=summary.read_text() if summary.exists() else '',
                 hitFiles={p.name:p.read_text() for p in (root/'results').glob('*hit*')})
        try:
            if timed_out:raise ValueError('sample timed out')
            check_sample(row)
        except ValueError as error:
            row['failureReason']=str(error)
            raise SampleFailure(row) from error
        return row


def summarize(result):
    if result.get('baselineSha256')!=BASELINE or result.get('candidateSha256')!=SUB:
        raise ValueError('wrong binary identities')
    expected=[]
    for name in sorted(NAMES):
        for sample in range(3):
            for label in (('baseline','candidate') if sample%2==0 else ('candidate','baseline')):
                expected.append((name,sample,label))
    actual=[(r['name'],r['sample'],r['binary']) for r in result['samples']]
    if actual!=expected:raise ValueError('missing, duplicate or noninterleaved sample')
    for row in result['samples']:check_sample(row)
    output={}
    for name in sorted(NAMES):
        times={label:[r['seconds'] for r in result['samples'] if r['name']==name and r['binary']==label]
               for label in ('baseline','candidate')}
        b,c=(statistics.median(times[label]) for label in ('baseline','candidate'))
        projections={label:max(values)*(FULL_RANGE/COUNT) for label,values in times.items()}
        output[name]=dict(seconds=times,throughputGainPercent=100*(b/c-1),wallTimeReductionPercent=100*(1-c/b),
                          projectedFullRangeSeconds=projections,projectionMethod='maximum startup-inclusive sample scaled linearly',
                          candidateWithin840SecondWorkerLimit=projections['candidate']<840)
        if projections['candidate']>=840:
            raise ValueError('candidate projected full range exceeds worker limit')
    return output


def sync_directory(path):
    fd=os.open(path,os.O_RDONLY)
    try:os.fsync(fd)
    finally:os.close(fd)


def save(path,result):
    temporary=path.with_suffix('.tmp')
    with temporary.open('w') as stream:
        json.dump(result,stream,indent=2);stream.flush();os.fsync(stream.fileno())
    temporary.replace(path)
    sync_directory(path.parent)


def main():
    bundle,output,fixture_hash=Path(sys.argv[1]),Path(sys.argv[2]),sys.argv[3]
    baseline=(bundle/'baseline/subset').resolve();candidate=Path('/opt/qsb/subset')
    for path,expected in ((baseline,BASELINE),(candidate,SUB)):
        if hashlib.sha256(path.read_bytes()).hexdigest()!=expected:raise ValueError('binary hash mismatch')
    raw=(bundle/'fixtures.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=fixture_hash:raise ValueError('fixture hash mismatch')
    fixtures=json.loads(raw)['benchmark']
    if len(fixtures)!=4 or {f['name'] for f in fixtures}!=NAMES:raise ValueError('fixture inventory mismatch')
    sys.path.insert(0,'/opt/qsb');import handler
    binding=handler.release_binding();validate_binding(binding)
    gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines())!=1 or 'A10G' not in gpu:raise ValueError('one A10G required')
    result=dict(status='running',baselineSha256=BASELINE,candidateSha256=SUB,binding=binding,gpu=gpu,
                fixtureSha256=fixture_hash,samples=[],freshWithdrawal=False,grantsRangeCredit=False)
    with output.open('x') as stream:
        json.dump(result,stream);stream.flush();os.fsync(stream.fileno())
    sync_directory(output.parent)
    deadline=time.monotonic()+600
    try:
        for fixture in sorted(fixtures,key=lambda f:f['name']):
            for sample in range(3):
                order=[('baseline',baseline),('candidate',candidate)]
                if sample%2:order.reverse()
                for label,binary in order:
                    row=execute(binary,fixture,deadline)
                    result['samples'].append(dict(name=fixture['name'],sample=sample,binary=label,**row));save(output,result)
        result['summary']=summarize(result);result['status']='completed';save(output,result)
    except BaseException as error:
        result['status']='failed';result['errorType']=type(error).__name__
        if isinstance(error,SampleFailure):result['failedSample']=dict(name=fixture['name'],sample=sample,binary=label,**error.row)
        save(output,result);raise
    print(json.dumps(dict(status='completed',samples=len(result['samples']),resultSha256=hashlib.sha256(output.read_bytes()).hexdigest())))


if __name__=='__main__':main()
