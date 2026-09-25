"""Matched frozen pinning binaries on synthetic public inputs; never range credit."""
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
from run_a10g import validate_binding
from run_a10g_performance import save, SampleFailure

BASELINE='f97d6a95a57841a619f1b842e3007320af1c0ff17f60366bb1b8b80912fe40e0'
CANDIDATE='cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62'
COUNT=256_000_000
FULL_RANGE=19_913_600_000
NAMES={'wpkh-pinning','taproot-pinning'}
ARGS=['0','1','0','single_hash','seq_start=2147483648','seq_count=1',
      'lt_start=500000000',f'lt_count={COUNT}']

def check(row):
    if row['arguments']!=ARGS or row['count']!=COUNT:raise ValueError('wrong bounds')
    if type(row['seconds']) not in (int,float) or not math.isfinite(row['seconds']) or not 0<row['seconds']<=40:
        raise ValueError('invalid timing')
    if row['exit']!=0 or row['timedOut'] or row['hitFiles'] or 'QSB_RANGE_INCOMPLETE' in row['log']:
        raise ValueError('failed or hit-producing sample')
    # Frozen binaries print integer millions. Exact requested bounds are bound
    # separately; this rounded counter alone is not exact coverage certification.
    done=re.findall(r'^\s*Done: (\d+)M in \d+s \([0-9.]+M/s\), found=(\d+)\s*$',row['log'],re.M)
    if done!=[(str(COUNT//1_000_000),'0')]:raise ValueError('missing/short completion')
    scope=re.findall(r'=== Search: lt=\[500000000,1744600000\] \(256000000\), seq=\[0x80000000\+\], GPU 0 \(global 0 of 1\) ===',row['log'])
    if len(scope)!=1:raise ValueError('wrong effective bounds')

def execute(binary,fixture,deadline):
    remaining=min(40,deadline-time.monotonic())
    if remaining<=0:raise TimeoutError('deadline')
    raw=base64.b64decode(fixture['params'],validate=True)
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);(root/'params.bin').write_bytes(raw)
        start=time.monotonic()
        proc=subprocess.Popen([str(binary),'params.bin',*ARGS],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
        timed=False
        try:output,_=proc.communicate(timeout=remaining)
        except subprocess.TimeoutExpired:
            timed=True
            try:os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            output,_=proc.communicate()
        except BaseException:
            try:os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            proc.communicate();raise
        row=dict(arguments=ARGS,count=COUNT,seconds=time.monotonic()-start,exit=proc.returncode,timedOut=timed,
                 paramsSha256=hashlib.sha256(raw).hexdigest(),log=output.decode(errors='replace'),
                 hitFiles={p.name:p.read_text() for p in (root/'results').glob('*hit*')})
        try:check(row)
        except ValueError as error:
            row['failureReason']=str(error);raise SampleFailure(row) from error
        return row

def summarize(result):
    if result['baselineSha256']!=BASELINE or result['candidateSha256']!=CANDIDATE:raise ValueError('wrong identities')
    expected=[(name,i,label) for name in sorted(NAMES) for i in range(3)
              for label in (('baseline','candidate') if i%2==0 else ('candidate','baseline'))]
    if [(r['name'],r['sample'],r['binary']) for r in result['samples']]!=expected:raise ValueError('incomplete/interleaving mismatch')
    out={}
    for name in sorted(NAMES):
        rows=[r for r in result['samples'] if r['name']==name]
        for r in rows:check(r)
        if len({r['paramsSha256'] for r in rows})!=1:raise ValueError('different parameters')
        times={label:[r['seconds'] for r in rows if r['binary']==label] for label in ('baseline','candidate')}
        projection=max(times['candidate'])*FULL_RANGE/COUNT
        if projection>=840:raise ValueError('candidate projected worker timeout')
        out[name]=dict(seconds=times,throughputGainPercent=100*(statistics.median(times['baseline'])/statistics.median(times['candidate'])-1),
                       projectedCandidateFullRangeSeconds=projection,projectionMethod='slowest startup-inclusive sample scaled linearly; not full-range measurement')
    return out

def main():
    bundle,output,expected=Path(sys.argv[1]),Path(sys.argv[2]),sys.argv[3]
    raw=(bundle/'pinning-fixtures.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=expected:raise ValueError('fixture hash')
    fixtures=json.loads(raw)
    if len(fixtures)!=2 or {f['name'] for f in fixtures}!=NAMES:raise ValueError('fixture inventory')
    binaries={'baseline':bundle/'baseline/pinning','candidate':Path('/opt/qsb/pinning')}
    for label,digest in [('baseline',BASELINE),('candidate',CANDIDATE)]:
        if hashlib.sha256(binaries[label].read_bytes()).hexdigest()!=digest:raise ValueError('binary hash')
    sys.path.insert(0,'/opt/qsb');import handler
    binding=handler.release_binding();validate_binding(binding)
    gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,driver_version','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines())!=1 or 'A10G' not in gpu:raise ValueError('one A10G required')
    result=dict(status='running',baselineSha256=BASELINE,candidateSha256=CANDIDATE,binding=binding,gpu=gpu,
                fixtureSha256=expected,samples=[],grantsRangeCredit=False,freshWithdrawal=False)
    with output.open('x') as f:json.dump(result,f);f.flush();os.fsync(f.fileno())
    deadline=time.monotonic()+600
    try:
        for fixture in sorted(fixtures,key=lambda f:f['name']):
            for sample in range(3):
                for label in (('baseline','candidate') if sample%2==0 else ('candidate','baseline')):
                    row=execute(binaries[label],fixture,deadline)
                    result['samples'].append(dict(row,name=fixture['name'],sample=sample,binary=label));save(output,result)
        result['summary']=summarize(result);result['status']='completed';save(output,result)
    except BaseException as error:
        result['status']='failed';result['errorType']=type(error).__name__
        if isinstance(error,SampleFailure):result['failedSample']=dict(error.row,name=fixture['name'],sample=sample,binary=label)
        save(output,result);raise

if __name__=='__main__':main()
