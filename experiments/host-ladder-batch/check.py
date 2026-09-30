"""Run a bounded fixed public dataset and all four expected failure cases."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

def run_capture(arguments, output, name, timeout):
    def as_text(value):
        return value.decode('utf-8', errors='replace') if isinstance(value, bytes) else (value or '')
    try:
        result=subprocess.run(arguments,capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired as error:
        (output/(name+'.stdout')).write_text(as_text(error.stdout))
        (output/(name+'.stderr')).write_text(as_text(error.stderr))
        evidence={'schema':1,'status':'failed','stage':name,'reason':'timeout','timeout_seconds':timeout}
        (output/(name+'.terminal.json')).write_text(json.dumps(evidence,indent=2)+'\n')
        (output/'failure.json').write_text(json.dumps(evidence,indent=2)+'\n')
        raise ValueError(f'{name} timed out; partial outputs preserved') from error
    (output/(name+'.stdout')).write_text(as_text(result.stdout))
    (output/(name+'.stderr')).write_text(as_text(result.stderr))
    (output/(name+'.terminal.json')).write_text(json.dumps({'schema':1,'stage':name,'exit':result.returncode},indent=2)+'\n')
    return result

def check(binary, output):
    output.mkdir(parents=True,exist_ok=False)
    binary=binary.resolve()
    r=run_capture([str(binary),str(output/'result.json')],output,'normal',120)
    if r.returncode: raise ValueError('normal public fixtures failed')
    data=json.loads((output/'result.json').read_text())
    if data['status']!='passed' or len(data['fixtures'])!=5 or not all(x['all_records_equal'] is True and x['public_fixture']==i for i,x in enumerate(data['fixtures'])): raise ValueError('incomplete result')
    for key,value in [('records_per_fixture',19200),('populated_per_fixture',12002),('padding_per_fixture',7198),('samples_per_fixture',90)]:
        if data.get(key)!=value: raise ValueError('unexpected geometry or oracle coverage')
    modes=['--reject-baseline-zero','--reject-batch-zero','--reject-baseline-order','--reject-batch-order']
    errors=[]
    for mode in modes:
        r=run_capture([str(binary),mode],output,mode.removeprefix('--'),10)
        if r.returncode!=2 or r.stderr.count('QSB_RANGE_INCOMPLETE: OpenSSL table operation failed') != 1: raise ValueError(f'expected rejection missing: {mode}')
        errors.append({'mode':mode,'exit':r.returncode,'stderr':r.stderr})
    report={'schema':1,'status':'passed','binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'normal_sha256':hashlib.sha256((output/'result.json').read_bytes()).hexdigest(),'expected_rejections':errors,'scope':'fixed public point ladders only; no solver or throughput claim'}
    (output/'checks.json').write_text(json.dumps(report,indent=2)+'\n')
    return report
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('binary',type=Path);p.add_argument('output',type=Path);a=p.parse_args();check(a.binary,a.output)
