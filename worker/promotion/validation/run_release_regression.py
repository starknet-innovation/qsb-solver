"""Exact installed image smoke plus source-locked trace; no durable credit."""
import base64
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from benchmark import execute, hit_fields

COMMIT='bef76bf9aec123d95fdff53fb839a0c44f378927'
PIN='4602c9845d7db1336b5ad00d67348063dce2c164bed3005ba18624f8c3dc6fa7'
SUB='1c7d6b5906e95c12f07faf08f93cfe5ca920974c9cb936909548b81b82dade3a'


def main():
    root=Path(sys.argv[1]);out=Path(sys.argv[2])
    sys.path.insert(0,'/opt/qsb');import handler
    binding=handler.release_binding()
    if binding['solverCommit']!=COMMIT or binding['files']['pinning']!=PIN or binding['files']['subset']!=SUB:
        raise ValueError('wrong final image binding')
    receipt=json.loads((root/'receipt.json').read_text())
    if receipt['unmodifiedBinarySha256']!=SUB or receipt['sourceLockSha256']!=binding['subsetSourceLockSha256']:
        raise ValueError('trace not bound to installed subset')
    if set(receipt['files'])!={'trace-subset','trace.diff'}:raise ValueError('trace inventory mismatch')
    for n,h in receipt['files'].items():
        if hashlib.sha256((root/n).read_bytes()).hexdigest()!=h:raise ValueError('trace artifact mismatch')
    (root/'trace-subset').chmod(0o700)
    fixtures=json.loads((root/'fixtures.json').read_text())
    deadline=time.monotonic()+1100
    result=dict(binding=binding,traceReceipt=receipt,worker=[],ranges=[],replays=[])
    for request in fixtures['requests']:
        code='import json,sys;sys.path.insert(0,"/opt/qsb");from handler import handler;print(json.dumps(handler(json.load(sys.stdin))))'
        p=subprocess.run([sys.executable,'-c',code],input=json.dumps({'input':request}),text=True,capture_output=True,timeout=min(180,deadline-time.monotonic()),check=True)
        row=json.loads(p.stdout)
        if row['status']!='completed' or row['checkpoint']!='range-complete' or row['candidates'] or row['verified'] is not False:
            raise ValueError('worker failed or unexpected hit requires CPU verification')
        for k in ['kernelCommit','stage','manifestHash','attempt']:
            if row[k]!=request[k]:raise ValueError('worker context mismatch')
        from search_ranges import work_range
        if row['workRange']!=work_range(request['stage'],request['attempt']):raise ValueError('range mismatch')
        result['worker'].append(row);print('WORKER',row['stage'],'PASS',flush=True)
    for fixture in fixtures['cases']:
        rows={}
        for label,binary in [('trace',root/'trace-subset'),('exact',Path('/opt/qsb/subset'))]:
            row=execute(binary,fixture,fixture['count'],fixture['start'],deadline)
            if row['hit']:raise ValueError('new hit requires independent verification')
            rows[label]=row
        result['ranges'].append(dict(name=fixture['name'],**rows));print('RANGE',fixture['name'],'PASS',flush=True)
    for fixture in fixtures['replays']:
        row=execute(Path('/opt/qsb/subset'),fixture,1,fixture['rank'],deadline)
        if hit_fields(row['hit'])!=hit_fields(fixture['expected']):raise ValueError('historical replay mismatch')
        result['replays'].append(dict(name=fixture['name'],**row))
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('QSB_REGRESSION_PASS',hashlib.sha256(out.read_bytes()).hexdigest(),flush=True)


if __name__=='__main__':main()
