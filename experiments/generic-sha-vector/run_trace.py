"""Bounded trace collection; independent CPU/full-transaction verdict remains separate."""
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import sys
import time
from run_pair import SUB, execute, save, sync_directory, SampleFailure
from trace_source import CANDIDATE_TREE

FIXTURES='e9e4f2abfdb27195f9e67d18b86990fc9419008084a9a142f24e127a89be1104'


def unrank(rank):
    if not 0 <= rank < math.comb(150,9):raise ValueError('rank outside domain')
    result=[];low=0
    for k in range(9,0,-1):
        for v in range(low,150):
            count=math.comb(149-v,k-1)
            if rank<count:
                result.append(v);low=v+1;break
            rank-=count
    return tuple(result)


def trace_records(log, start, count):
    records={}
    for line in log.splitlines():
        if not line.startswith('TRACE_SUB'):continue
        match=re.fullmatch(r'TRACE_SUB indices=([0-9,]+) recid=([01]) hash=([a-f0-9]{64})',line)
        if not match:raise ValueError('malformed trace')
        key=(tuple(map(int,match[1].split(','))),int(match[2]))
        if key in records:raise ValueError('duplicate trace')
        records[key]=match[3]
    expected={(unrank(rank),bit) for rank in range(start,start+count) for bit in (0,1)}
    if set(records)!=expected:raise ValueError('trace does not cover exact requested range')
    return records


def main():
    bundle,output,receipt_hash=Path(sys.argv[1]),Path(sys.argv[2]),sys.argv[3]
    raw=(bundle/'trace-receipt.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=receipt_hash:raise ValueError('receipt mismatch')
    receipt=json.loads(raw)
    if receipt['unmodifiedBinarySha256']!=SUB or receipt['unmodifiedTreeSha256']!=CANDIDATE_TREE:
        raise ValueError('wrong candidate binding')
    if set(receipt['files'])!={'candidate-trace','candidate-trace.diff'}:raise ValueError('wrong trace inventory')
    for name,want in {**receipt['files'],'candidate':SUB}.items():
        if hashlib.sha256((bundle/name).read_bytes()).hexdigest()!=want:raise ValueError('artifact mismatch')
    raw=(bundle/'trace-fixtures.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=FIXTURES:raise ValueError('fixture mismatch')
    cases=json.loads(raw)['cases']
    if len(cases)!=20 or len({c['name'] for c in cases})!=20:raise ValueError('wrong cases')
    gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,driver_version','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines())!=1 or 'A10G' not in gpu:raise ValueError('one A10G required')
    result=dict(status='running',traceReceipt=receipt,receiptSha256=receipt_hash,fixtureSha256=FIXTURES,
                candidateSha256=SUB,gpu=gpu,ranges=[],cpuVerified=False,freshWithdrawal=False,grantsRangeCredit=False)
    with output.open('x') as stream:
        import os
        json.dump(result,stream);stream.flush();os.fsync(stream.fileno())
    sync_directory(output.parent)
    deadline=time.monotonic()+600
    context={}
    try:
        for case in cases:
            rows={}
            for label,name in [('trace','candidate-trace'),('exact','candidate')]:
                context=dict(name=case['name'],binary=label)
                row=execute((bundle/name).resolve(),case,deadline,count=case['count'],rank=case['start'])
                if label=='trace':trace_records(row['log'],case['start'],case['count'])
                rows[label]=row
            result['ranges'].append(dict(name=case['name'],**rows));save(output,result)
        result['status']='native-completed-awaiting-cpu-verification';save(output,result)
    except BaseException as error:
        result.update(status='failed',errorType=type(error).__name__,failedContext=context)
        if isinstance(error,SampleFailure):result['failedSample']=error.row
        save(output,result);raise
    print(json.dumps(dict(status=result['status'],cases=len(result['ranges']),resultSha256=hashlib.sha256(output.read_bytes()).hexdigest())))


if __name__=='__main__':main()
