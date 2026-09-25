"""Native bounded host-error audit. Requires an external resource watchdog."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

CALL = re.compile(r'^QSB_AUDIT_CALL (\d+) (.+)$', re.M)


def run(binary, params, extra, env=None):
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp); (root/'results').mkdir()
        clean={k:v for k,v in os.environ.items() if not k.startswith('QSB_AUDIT_')}
        clean.update(env or {})
        proc=subprocess.run([str(binary),str(params),'0','1','0','single_hash',*extra],
                            cwd=root,env=clean,text=True,capture_output=True,timeout=90)
        hits={p.name:p.read_text() for p in (root/'results').iterdir() if p.is_file()}
        return dict(exit=proc.returncode,stdout=proc.stdout,stderr=proc.stderr,hits=hits)


def validate_failure(result, expected_calls=None):
    if result['exit'] != 2 or 'Done:' in result['stdout'] or 'QSB_RANGE_INCOMPLETE' not in result['stderr'] or result['hits']:
        raise ValueError('fault did not fail closed before completion/hit publication')
    if expected_calls is not None and CALL.findall(result['stderr']) != expected_calls:
        raise ValueError('fault reached unexpected later calls or changed call sequence')


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--artifacts',type=Path,required=True)
    parser.add_argument('--params',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    artifacts=args.artifacts.resolve(); params=args.params.resolve()
    receipt=json.loads((artifacts/'receipt.json').read_text())
    if set(receipt['files']) != {'pinning','pinning-audit'}:
        raise ValueError('unexpected artifact inventory')
    for name,expected in receipt['files'].items():
        path=artifacts/name
        if hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
            raise ValueError('artifact hash mismatch')
        path.chmod(0o700)
    extra=['seq_start=2147483648','seq_count=1','lt_start=500000000','lt_count=256']
    begin=time.monotonic()
    normal=run(artifacts/'pinning',params,extra)
    diagnostic=run(artifacts/'pinning-audit',params,extra)
    for result in [normal,diagnostic]:
        if result['exit'] or 'Done:' not in result['stdout']:
            raise ValueError('baseline did not complete')
        if result['hits']:
            raise ValueError('unexpected real hit requires independent CPU verification')
    calls=CALL.findall(diagnostic['stderr'])
    if not calls or [int(x[0]) for x in calls]!=list(range(1,len(calls)+1)):
        raise ValueError('diagnostic call sequence invalid')
    failures=[]
    for i in range(1,len(calls)+1):
        if time.monotonic()-begin>1200:
            raise TimeoutError('20 minute audit deadline reached')
        result=run(artifacts/'pinning-audit',params,extra,{'QSB_AUDIT_FAIL':str(i)})
        validate_failure(result,calls[:i]); failures.append(result)
    overflow=run(artifacts/'pinning-audit',params,extra,{'QSB_AUDIT_OVERFLOW':'1'})
    validate_failure(overflow)
    args.output.write_text(json.dumps(dict(status='PASS',receipt=receipt,
        paramsSha256=hashlib.sha256(params.read_bytes()).hexdigest(),arguments=extra,
        normal=normal,diagnostic=diagnostic,faults=failures,overflow=overflow,
        scope='Bounded native host-failure injection; not full search or withdrawal proof'),indent=2)+'\n')
    print(json.dumps(dict(status='PASS',reachedCalls=len(calls),overflowRejected=True)))


if __name__ == '__main__':
    main()
