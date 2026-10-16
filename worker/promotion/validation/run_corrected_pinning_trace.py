"""Bounded, hash-bound pinning diagnostic and unchanged-binary boundary gate."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from corrected_pinning_trace import VERSION, sha, verify_trace
from run_edge_audit import run as execute

NORMAL_SHA256='cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62'
TIMING_COUNTS=(1 << 20, 1 << 24, 1 << 26)
DEFAULT_RANGE_COUNT=19913600000
EXPECTED_CASES=[(seq,lt) for seq in (0x80000000,0xffffffff)
                for lt in (500000000,500000063,500000127,500000255,1744599996)]


def validate_plan(plan):
    if plan.get('scriptVersion') != VERSION or plan.get('status') != 'PREPARED_NOT_EXECUTED':
        raise ValueError('Wrong corrected plan version/status')
    raw=base64.b64decode(plan['parameterBase64'],validate=True)
    if hashlib.sha256(raw).hexdigest()!=plan['parameterSha256']:
        raise ValueError('Parameter hash mismatch')
    cases=plan['cases']
    if [(c['sequence'],c['locktime']) for c in cases] != EXPECTED_CASES or plan['expectedHashes']!=80:
        raise ValueError('Wrong boundary inventory')
    for case in cases:
        if case['sequenceCount']!=1 or case['locktimeCount']!=4:
            raise ValueError('Unbounded pinning case')
        keys={f"{case['sequence']}:{lt}:{recid}" for lt in range(case['locktime'],case['locktime']+4) for recid in (0,1)}
        if set(case['expected'])!=keys or any(not re.fullmatch('[0-9a-f]{64}',h) for h in case['expected'].values()):
            raise ValueError('Wrong expected hash inventory')
    return plan


def validate_receipt(path, expected_sha, normal):
    if sha(path)!=expected_sha or sha(normal)!=NORMAL_SHA256:
        raise ValueError('Receipt or exact candidate binary mismatch')
    receipt=json.loads(path.read_text())
    files=receipt.get('files',{})
    if receipt.get('architecture')!='sm_86' or receipt.get('flags')!=['-O3','-arch=sm_86','-DQSB_SLOTPIPE=0']:
        raise ValueError('Wrong diagnostic build flags/architecture')
    if set(files)!={'pinning','pinning-trace','trace.diff'} or files['pinning']!=NORMAL_SHA256:
        raise ValueError('Diagnostic normal binary does not match exact candidate')
    for name,digest in files.items():
        artifact=path.parent/name
        if artifact.is_symlink() or sha(artifact)!=digest:
            raise ValueError('Diagnostic artifact mismatch')
    return receipt


def timing_summary(rows):
    if [r['count'] for r in rows] != list(TIMING_COUNTS) or any(r['seconds']<=0 for r in rows):
        raise ValueError('Incomplete timing inventory')
    largest=rows[-1]
    # Includes process startup scaled with work: deliberately conservative for
    # this sampled single-sequence geometry, not proof for the 16-sequence range.
    projected=DEFAULT_RANGE_COUNT*largest['seconds']/largest['count']
    return dict(defaultRangeCandidates=DEFAULT_RANGE_COUNT,
                projectedSecondsAtLargestProcessRate=projected,
                fits840SecondsWithDoubleTimeMargin=projected*2<840,
                scope='Single-sequence real-predicate process timing; extrapolation only, not full 16-sequence range completion or coverage credit')


def run(plan_path, plan_sha, receipt_path, receipt_sha, normal, output, deadline_epoch, timing=False):
    if sha(plan_path)!=plan_sha:
        raise ValueError('Plan identity mismatch')
    plan=validate_plan(json.loads(plan_path.read_text()))
    receipt=validate_receipt(receipt_path,receipt_sha,normal)
    remaining=deadline_epoch-time.time()
    if remaining<660:
        raise ValueError('At least 660 seconds before fixed campaign stop required')
    deadline=time.monotonic()+600
    result=dict(status='RUNNING',planSha256=plan_sha,traceReceiptSha256=receipt_sha,
                normalSha256=NORMAL_SHA256,traceReceipt=receipt,ranges=[],timing=[],freshWithdrawal=False,
                limits='80 diagnostic recovered-key hash comparisons and exact-binary boundary smokes; no real-hit or full-domain proof')
    with output.open('x') as stream:
        json.dump(result,stream)
    try:
        gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True,timeout=10).strip()
        if len(gpu.splitlines())!=1 or 'A10G' not in gpu:
            raise ValueError('Exactly one A10G required')
        result['gpu']=gpu
        for case in plan['cases']:
            rows=dict(sequence=case['sequence'],locktime=case['locktime'],sequenceCount=1,locktimeCount=4)
            result['ranges'].append(rows)
            args=['0','1','0','single_hash',f"seq_start={case['sequence']}",'seq_count=1',f"lt_start={case['locktime']}",'lt_count=4']
            for label,binary in [('trace',receipt_path.parent/'pinning-trace'),('normal',normal)]:
                if time.monotonic()>=deadline:
                    raise TimeoutError('Pinning gate deadline')
                started=time.monotonic()
                row=execute(binary,plan['parameterBase64'],args,deadline)
                row['seconds']=time.monotonic()-started
                rows[label]=row
                if row['exit'] or row['hits'] or 'Mode: REAL' not in row['log'] or 'Done:' not in row['log'] or 'QSB_RANGE_INCOMPLETE' in row['log']:
                    raise ValueError('Native pinning case failed or real hit requires independent CPU validation')
                if label=='trace':
                    row['cpuHashesVerified']=verify_trace(row['log'],case['expected'])
        if timing:
            for count in TIMING_COUNTS:
                if time.monotonic()>=deadline:
                    raise TimeoutError('Pinning timing deadline')
                args=['0','1','0','single_hash','seq_start=2147483648','seq_count=1',
                      'lt_start=500000000',f'lt_count={count}']
                started=time.monotonic()
                row=execute(normal,plan['parameterBase64'],args,deadline)
                row.update(count=count,seconds=time.monotonic()-started)
                result['timing'].append(row)
                if row['exit'] or row['hits'] or 'Mode: REAL' not in row['log'] or 'Done:' not in row['log'] or 'QSB_RANGE_INCOMPLETE' in row['log']:
                    raise ValueError('Timing failed or real hit requires independent CPU validation')
            result['timingSummary']=timing_summary(result['timing'])
        result['status']='BOUNDED_PINNING_NATIVE_PASS'
    except Exception as exc:
        result['status']='FAILED';result['error']=str(exc)
        raise
    finally:
        temporary=output.with_suffix(output.suffix+'.tmp')
        temporary.write_text(json.dumps(result,indent=2)+'\n');temporary.replace(output)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('plan','receipt','normal','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    for name in ('plan-sha256','receipt-sha256'):
        parser.add_argument('--'+name,required=True)
    parser.add_argument('--deadline-epoch',type=int,required=True)
    parser.add_argument('--timing',action='store_true',help='Add three bounded real-predicate process timing samples')
    args=parser.parse_args()
    run(args.plan.resolve(),args.plan_sha256,args.receipt.resolve(),args.receipt_sha256,
        args.normal.resolve(),args.output.resolve(),args.deadline_epoch,args.timing)


if __name__=='__main__':main()
