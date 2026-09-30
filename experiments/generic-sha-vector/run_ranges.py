"""Sampled full-binary range regression, not CPU differential or whole-domain proof."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from run_pair import BASELINE, SUB, NAMES, SampleFailure, check_sample, execute, save, sync_directory

FIXTURES = 'e7975d3061ccd7246c0d4548eeab201710a93959b63a2fcbd3a602e9790b99b9'
RANGES = ((0, 1), (63, 257), (65535, 65537), (0, 2**26))


def validate(result):
    if (result.get('baselineSha256'), result.get('candidateSha256'), result.get('fixtureSha256')) != (BASELINE, SUB, FIXTURES):
        raise ValueError('wrong regression identities')
    expected = [(name, rank, count, label) for name in sorted(NAMES)
                for rank, count in RANGES for label in ('baseline', 'candidate')]
    rows = result['samples']
    if [(r['name'], r['rank'], r['count'], r['binary']) for r in rows] != expected:
        raise ValueError('incomplete regression inventory')
    for row in rows:
        check_sample(row, row['count'], row['rank'])


def main():
    bundle, output = Path(sys.argv[1]), Path(sys.argv[2])
    binaries = [('baseline', (bundle/'baseline').resolve()), ('candidate', (bundle/'candidate').resolve())]
    for (_, path), expected in zip(binaries, (BASELINE, SUB)):
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('binary hash mismatch')
    raw = (bundle/'fixtures.json').read_bytes()
    if hashlib.sha256(raw).hexdigest() != FIXTURES:
        raise ValueError('fixture hash mismatch')
    fixtures = json.loads(raw)['benchmark']
    if len(fixtures) != 4 or {f['name'] for f in fixtures} != NAMES:
        raise ValueError('wrong fixture inventory')
    gpu = subprocess.check_output(['nvidia-smi', '--query-gpu=name,driver_version', '--format=csv,noheader'], text=True).strip()
    if len(gpu.splitlines()) != 1 or 'A10G' not in gpu:
        raise ValueError('one A10G required')
    result = dict(status='running', baselineSha256=BASELINE, candidateSha256=SUB,
                  fixtureSha256=FIXTURES, gpu=gpu, samples=[], grantsRangeCredit=False,
                  freshWithdrawal=False, cpuDifferential=False)
    with output.open('x') as stream:
        json.dump(result, stream)
        stream.flush()
        import os
        os.fsync(stream.fileno())
    sync_directory(output.parent)
    deadline = time.monotonic()+600
    context = {}
    try:
        for fixture in sorted(fixtures, key=lambda f: f['name']):
            for rank, count in RANGES:
                for label, binary in binaries:
                    context = dict(name=fixture['name'], binary=label)
                    row = execute(binary, fixture, deadline, count=count, rank=rank)
                    result['samples'].append(dict(**context, **row))
                    save(output, result)
        validate(result)
        result['status'] = 'completed'
        save(output, result)
    except BaseException as error:
        result.update(status='failed', errorType=type(error).__name__)
        if isinstance(error, SampleFailure):
            result['failedSample'] = dict(**context, **error.row)
        save(output, result)
        raise
    print(json.dumps(dict(status='completed', samples=len(result['samples']), resultSha256=hashlib.sha256(output.read_bytes()).hexdigest())))


if __name__ == '__main__':
    main()
