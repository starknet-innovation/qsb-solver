"""Bounded sm86 trace/exact-binary runs; verdict requires separate CPU verification."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from benchmark import execute
from run_a10g import validate_binding, SUB


def validate_trace(receipt, binding):
    validate_binding(binding)
    if receipt.get('architecture') != 'sm_86' or receipt.get('unmodifiedBinarySha256') != SUB:
        raise ValueError('trace not bound to exact sm86 binary')
    if receipt.get('sourceLockSha256') != binding.get('subsetSourceLockSha256'):
        raise ValueError('trace source lock mismatch')
    if set(receipt.get('files', {})) != {'trace-subset', 'trace.diff'}:
        raise ValueError('trace artifact inventory mismatch')


def main():
    root = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2])
    receipt_path = root/'receipt.json'
    if hashlib.sha256(receipt_path.read_bytes()).hexdigest() != sys.argv[3]:
        raise ValueError('unexpected trace receipt')
    sys.path.insert(0, '/opt/qsb')
    import handler
    binding = handler.release_binding()
    receipt = json.loads(receipt_path.read_text())
    validate_trace(receipt, binding)
    for name, expected in receipt['files'].items():
        p = root/name
        if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest() != expected:
            raise ValueError('trace file mismatch')
    fixtures_path = Path(__file__).with_name('trace-fixtures.json')
    if hashlib.sha256(fixtures_path.read_bytes()).hexdigest() != sys.argv[4]:
        raise ValueError('fixture identity mismatch')
    cases = json.loads(fixtures_path.read_text())['cases']
    if len(cases) != 20 or len({c['name'] for c in cases}) != 20:
        raise ValueError('incomplete fixture inventory')
    gpu = subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines()) != 1 or 'A10G' not in gpu:
        raise ValueError('exactly one A10G required')
    with output.open('x') as stream:
        json.dump({'status':'running','binding':binding},stream)
    result = dict(status='running',binding=binding,traceReceipt=receipt,gpu=gpu,ranges=[],cpuVerified=False,freshWithdrawal=False)
    deadline = time.monotonic()+600
    for fixture in cases:
        rows = {}
        for label,binary in [('trace',root/'trace-subset'),('exact',Path('/opt/qsb/subset'))]:
            row = execute(binary,fixture,fixture['count'],fixture['start'],deadline)
            if row['hit']:
                raise ValueError('unexpected hit requires independent CPU verification')
            rows[label] = row
        result['ranges'].append(dict(name=fixture['name'],**rows))
        print('RANGE',fixture['name'],'completed',flush=True)
    result['status'] = 'native-completed-awaiting-cpu-verification'
    tmp = output.with_suffix('.tmp');tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(output)
    print('QSB_TRACE_RESULT_SHA256='+hashlib.sha256(output.read_bytes()).hexdigest(),flush=True)


if __name__ == '__main__':
    main()
