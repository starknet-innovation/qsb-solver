"""Bounded public-fixture benchmark; no wallet, network spend or range credit."""
import base64
import hashlib
import json
import os
import re
from pathlib import Path
import signal
import subprocess
import tempfile
import time
import urllib.request

BASELINE_SHA = 'c7cdd7afa8ff8495be90f9ae148e5ca68b9ad0f3521800cc8a77297a10cc366e'
CANDIDATE_SHA = '1c7d6b5906e95c12f07faf08f93cfe5ca920974c9cb936909548b81b82dade3a'
BASELINE_URL = 'https://github.com/starknet-innovation/qsb-solver/releases/download/candidate-20260925-1/validation-baseline-subset'


def hit_fields(text):
    fields = dict(line.split('=', 1) for line in text.strip().splitlines())
    required = {'indices', 'hash_choice', 'recid'}
    if not required <= fields.keys() or fields.keys() - required - {'combo_idx'}:
        raise ValueError('invalid hit record')
    return {key: fields[key] for key in required}


def checked_hash(path, expected):
    actual = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError('binary identity mismatch')
    return actual


def execute(binary, fixture, count, rank, deadline):
    remaining = min(120, deadline - time.monotonic())
    if remaining <= 0:
        raise TimeoutError('batch deadline')
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / 'params.bin').write_bytes(base64.b64decode(fixture['params'], validate=True))
        command = [str(binary), 'params.bin', '0', str(fixture['sequence']),
                   str(fixture['locktime']), '1', '0', 'single_hash',
                   f'rank_start={rank}', f'rank_count={count}']
        start = time.monotonic()
        process = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            output, _ = process.communicate(timeout=remaining)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
            raise TimeoutError('solver timeout')
        elapsed = time.monotonic() - start
        log = output.decode(errors='replace')
        if process.returncode != 0 or not re.search(r'\[GPU 0\] Done(?: enum)?:', log) or 'QSB_RANGE_INCOMPLETE' in log:
            raise RuntimeError(f'solver failed: {process.returncode}: {log[-1500:]}')
        hit = root / 'results/digest_hit_0.txt'
        return dict(seconds=elapsed, count=count, rank=rank,
                    hit=hit.read_text() if hit.exists() else '', log=log)


def main():
    deadline = time.monotonic() + 1200
    fixtures = json.loads(Path(__file__).with_name('fixtures.json').read_text())
    candidate = Path('/opt/qsb/subset')
    checked_hash(candidate, CANDIDATE_SHA)
    with tempfile.TemporaryDirectory() as tmp:
        baseline = Path(tmp) / 'baseline'
        with urllib.request.urlopen(BASELINE_URL, timeout=30) as response:
            data = response.read(10_000_001)
        if len(data) > 10_000_000:
            raise ValueError('baseline too large')
        baseline.write_bytes(data)
        checked_hash(baseline, BASELINE_SHA)
        baseline.chmod(0o700)
        result = dict(candidateSha256=CANDIDATE_SHA, baselineSha256=BASELINE_SHA,
                      gpu=subprocess.check_output(['nvidia-smi', '--query-gpu=name,uuid,driver_version', '--format=csv,noheader'], text=True).strip(), replay=[], samples=[])
        for fixture in fixtures['replay']:
            row = execute(candidate, fixture, 1, fixture['rank'], deadline)
            if hit_fields(row['hit']) != hit_fields(fixture['expected']):
                raise ValueError('known hit replay mismatch')
            result['replay'].append(dict(name=fixture['name'], **row))
        for fixture in fixtures['benchmark']:
            for sample in range(3):
                order = [('baseline', baseline), ('candidate', candidate)]
                if sample % 2:
                    order.reverse()
                for label, binary in order:
                    row = execute(binary, fixture, 1 << 31, 0, deadline)
                    result['samples'].append(dict(name=fixture['name'], sample=sample, binary=label, **row))
                    print('PROGRESS', fixture['name'], sample, label, round(row['seconds'], 3), flush=True)
        Path('/tmp/benchmark-result.json').write_text(json.dumps(result, indent=2))
        print('QSB_BENCHMARK_RESULT=' + json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
