"""Isolated matched pair timing for the SHA rotate-add candidate; no enrollment or range credit.

Ported from experiments/generic-sha-vector/run_pair.py at b96752330d6d376a5bb0ba97cb6b2abe37d4e9eb.
Changed: candidate identity, four pairs per context, prerequisite set, and a fixed decision rule.
"""
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
SUB = 'bba9c4af12d65de4ffeea7c202ae2f830e815855a1f45a9f62f398730a9e65e1'

BASELINE = '8664f41f3deeeb91b3d189db3df469570c83e90610e4b54a955e2a625486606c'
COUNT = 1 << 29
PAIRS = 4
# Fixed before any run: see A10G-PLAN.md.
MIN_ROUND1_GAIN_PERCENT = 2.0
MAX_ROUND2_LOSS_PERCENT = 0.5
FULL_RANGE = 1 << 34
NAMES = {'wpkh-round1','wpkh-round2','taproot-round1','taproot-round2'}


def check_sample(row, count=COUNT, rank=0):
    if row['count'] != count or row['rank'] != rank:
        raise ValueError('wrong sample range')
    seconds=row['seconds']
    if type(seconds) not in (int,float) or not math.isfinite(seconds) or not 0 < seconds <= 120:
        raise ValueError('invalid timing')
    if row.get('timedOut',False) is not False or row['exit'] != 0 or 'QSB_RANGE_INCOMPLETE' in row['log']:
        raise ValueError('failed sample')
    if len(re.findall(r'\[GPU 0\] Done enum:',row['log'])) != 1:
        raise ValueError('missing unique completion')
    statuses=re.findall(r'^STATUS=.*$',row['summary'],re.M)
    if len(statuses)!=1 or not re.fullmatch(r'STATUS=EXHAUSTED \d+ total_attempts='+str(count)+r' elapsed_s=\d+ hits=0',statuses[0]):
        raise ValueError('incomplete or shortened sample')
    if row['hitFiles'] or re.search(r'^HIT ',row['summary'],re.M):
        raise ValueError('unexpected hit requires CPU review')


class SampleFailure(RuntimeError):
    def __init__(self, row):
        super().__init__('sample failed; diagnostics retained')
        self.row=row


def execute(binary, fixture, deadline, count=COUNT, rank=0):
    remaining=min(120,deadline-time.monotonic())
    if remaining<=0:raise TimeoutError('benchmark deadline')
    with tempfile.TemporaryDirectory() as directory:
        root=Path(directory);(root/'params.bin').write_bytes(base64.b64decode(fixture['params'],validate=True))
        command=[str(binary),'params.bin','0',str(fixture['sequence']),str(fixture['locktime']),
                 '1','0','single_hash',f'rank_start={rank}',f'rank_count={count}']
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
        row=dict(count=count,rank=rank,seconds=seconds,exit=process.returncode,timedOut=timed_out,
                 log=output.decode(errors='replace'),summary=summary.read_text() if summary.exists() else '',
                 hitFiles={p.name:p.read_text() for p in (root/'results').glob('*hit*')})
        try:
            if timed_out:raise ValueError('sample timed out')
            check_sample(row,count,rank)
        except ValueError as error:
            row['failureReason']=str(error)
            raise SampleFailure(row) from error
        return row


def summarize(result):
    if result.get('baselineSha256')!=BASELINE or result.get('candidateSha256')!=SUB:
        raise ValueError('wrong binary identities')
    expected=[]
    for name in sorted(NAMES):
        for sample in range(PAIRS):
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
        output[name]=dict(seconds=times,firstPairIsColdStart=True,throughputGainPercent=100*(b/c-1),wallTimeReductionPercent=100*(1-c/b),
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


# SHA-256 of the committed session A and B receipts (evidence/), frozen on 10 November 2026 after both passed.
# A None value means not frozen: timing refuses to start.
PREREQUISITES = {'native-trace-cpu.json': '0af420a8f8cbf71eaae82d815d2e25811b4d5328760ca732d1b8918fb066e167', 'native-ranges.json': '2bb26076526dcc2cc39e2e9503e2a8186fc8027ad06b00f6f54baef694fe308d'}


def decide(summary):
    """Apply the rule fixed in A10G-PLAN.md to a completed summary."""
    round1=[v['throughputGainPercent'] for k,v in summary.items() if k.endswith('round1')]
    round2=[v['throughputGainPercent'] for k,v in summary.items() if k.endswith('round2')]
    if len(round1)!=2 or len(round2)!=2:raise ValueError('decision needs both layouts and both rounds')
    passed=min(round1)>=MIN_ROUND1_GAIN_PERCENT and min(round2)>=-MAX_ROUND2_LOSS_PERCENT
    return dict(rule=f'round1 median gain >= {MIN_ROUND1_GAIN_PERCENT}% for both layouts and round2 not more than {MAX_ROUND2_LOSS_PERCENT}% slower',
                minimumRound1GainPercent=min(round1),minimumRound2GainPercent=min(round2),
                outcome='worth-release-candidate-review' if passed else 'no-demonstrated-benefit')


def check_prerequisites(bundle):
    if any(value is None for value in PREREQUISITES.values()):
        raise ValueError('prerequisite receipts are not frozen')
    receipts = {}
    for name, expected in PREREQUISITES.items():
        raw = (bundle / name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != expected:
            raise ValueError('prerequisite receipt mismatch: ' + name)
        receipts[name] = json.loads(raw)
    trace = receipts['native-trace-cpu.json']
    if trace['status'] != 'passed' or trace['candidateSha256'] != SUB or trace['candidates'] != 3116 or trace['hashes'] != 6232:
        raise ValueError('native trace prerequisite failed')
    if (bundle / 'regression.json').read_bytes() != (bundle / 'native-ranges.json').read_bytes():
        raise ValueError('regression differs from frozen native receipt')
    return dict(PREREQUISITES)


def main():
    bundle,output,fixture_hash=Path(sys.argv[1]),Path(sys.argv[2]),sys.argv[3]
    baseline=(bundle/'baseline').resolve();candidate=(bundle/'candidate').resolve()
    for path,expected in ((baseline,BASELINE),(candidate,SUB)):
        if hashlib.sha256(path.read_bytes()).hexdigest()!=expected:raise ValueError('binary hash mismatch')
    prerequisite_hashes=check_prerequisites(bundle)
    raw=(bundle/'fixtures.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=fixture_hash:raise ValueError('fixture hash mismatch')
    from run_ranges import validate as validate_ranges
    regression_raw=(bundle/'regression.json').read_bytes()
    regression=json.loads(regression_raw)
    if regression.get('status')!='completed':raise ValueError('range regression not completed')
    validate_ranges(regression)
    if regression['fixtureSha256']!=fixture_hash:raise ValueError('regression fixture mismatch')
    fixtures=json.loads(raw)['benchmark']
    if len(fixtures)!=4 or {f['name'] for f in fixtures}!=NAMES:raise ValueError('fixture inventory mismatch')
    # Name and driver only: the UUID identifies the physical GPU and stays out of public evidence.
    gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,driver_version','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines())!=1 or 'A10G' not in gpu:raise ValueError('one A10G required')
    result=dict(status='running',baselineSha256=BASELINE,candidateSha256=SUB,gpu=gpu,
                prerequisiteSha256=prerequisite_hashes,fixtureSha256=fixture_hash,regressionSha256=hashlib.sha256(regression_raw).hexdigest(),samples=[],freshWithdrawal=False,grantsRangeCredit=False)
    with output.open('x') as stream:
        json.dump(result,stream);stream.flush();os.fsync(stream.fileno())
    sync_directory(output.parent)
    deadline=time.monotonic()+600
    try:
        for fixture in sorted(fixtures,key=lambda f:f['name']):
            for sample in range(PAIRS):
                order=[('baseline',baseline),('candidate',candidate)]
                if sample%2:order.reverse()
                for label,binary in order:
                    row=execute(binary,fixture,deadline)
                    result['samples'].append(dict(name=fixture['name'],sample=sample,binary=label,**row));save(output,result)
        result['summary']=summarize(result);result['decision']=decide(result['summary']);result['status']='completed';save(output,result)
    except BaseException as error:
        result['status']='failed';result['errorType']=type(error).__name__
        if isinstance(error,SampleFailure):result['failedSample']=dict(name=fixture['name'],sample=sample,binary=label,**error.row)
        save(output,result);raise
    print(json.dumps(dict(status='completed',samples=len(result['samples']),resultSha256=hashlib.sha256(output.read_bytes()).hexdigest())))


if __name__=='__main__':main()
