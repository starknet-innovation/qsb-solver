"""Memcheck frozen binaries and explicit diagnostic edges; never grants range credit."""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

PIN = '4602c9845d7db1336b5ad00d67348063dce2c164bed3005ba18624f8c3dc6fa7'
SUB = '1c7d6b5906e95c12f07faf08f93cfe5ca920974c9cb936909548b81b82dade3a'
SANITIZER = '/opt/compute-sanitizer/compute-sanitizer'


def validate_result(code, expected, log):
    summaries = re.findall(r'^========= ERROR SUMMARY: (\d+) errors?$', log, re.M)
    tool_failure = re.search(r'^=========.*(?:ERROR:|FATAL|failed|Failed|unsupported|Unsupported|Unable|No attachable)', log, re.M)
    if code != expected or not summaries or any(int(n) for n in summaries) or tool_failure:
        raise ValueError('memcheck failed or missing zero-error summary')


def main():
    root, output = map(Path, sys.argv[1:3])
    deadline = time.monotonic() + 1000
    for name, expected in [('pinning', PIN), ('subset', SUB)]:
        if hashlib.sha256((Path('/opt/qsb') / name).read_bytes()).hexdigest() != expected:
            raise ValueError('wrong frozen binary')
    receipt = json.loads((root / 'receipt.json').read_text())
    if receipt['unmodifiedBinarySha256'] != SUB:
        raise ValueError('wrong diagnostic lineage')
    for name in ['capacity', 'forced-exception', 'detected-exception']:
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != receipt['files'][name]:
            raise ValueError('diagnostic hash mismatch')
        (root / name).chmod(0o700)
    fixture = json.loads((root / 'fixtures.json').read_text())
    pin = fixture['pinning']
    common = ['0', '2147483648', '500000000', '1', '0', 'single_hash', 'rank_start=7']
    cases = [('pinning-known-hit', '/opt/qsb/pinning', pin['parameterBase64'],
              ['0', '1', '0', 'single_hash', f"seq_start={pin['sequence']}", 'seq_count=1',
               f"lt_start={pin['locktime']}", 'lt_count=1'], {}, 0)]
    cases.append(('subset-boundary', '/opt/qsb/subset', fixture['ordinaryParams'], common + ['rank_count=257'], {}, 0))
    for count in [64, 65, 1025]:
        cases.append((f'capacity-{count}', str(root / 'capacity'), fixture['ordinaryParams'],
                      common + ['rank_count=1100'], {'QSB_AUDIT_HITS': str(count)}, 2 if count > 64 else 0))
    for mode in ['forced-exception', 'detected-exception']:
        cases.append((mode, str(root / mode), fixture['exceptionParams'], common + ['rank_count=7'], {}, 0))
    results = []
    for name, binary, params, args, extra, expected in cases:
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            (work / 'params.bin').write_bytes(base64.b64decode(params, validate=True))
            env = {k: v for k, v in os.environ.items() if not k.startswith('QSB_AUDIT_')}
            env.update(extra)
            command = [SANITIZER, '--tool', 'memcheck', '--error-exitcode', '99', binary, 'params.bin', *args]
            proc = subprocess.Popen(command, cwd=work, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, text=True, start_new_session=True)
            try:
                stdout, stderr = proc.communicate(timeout=max(.1, min(180, deadline-time.monotonic())))
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate()
                raise
            validate_result(proc.returncode, expected, stderr)
            hits = {p.name: p.read_text() for p in (work / 'results').glob('*hit*.txt')}
            if name.startswith('capacity-'):
                count = int(name.split('-')[1])
                if f'DEVICE_COUNT {count} CANARIES_OK' not in stdout:
                    raise ValueError('capacity kernel path not reached')
                if expected == 2 and 'QSB_RANGE_INCOMPLETE: hit count exceeds host capacity' not in stderr:
                    raise ValueError('wrong overflow failure')
            if name in ['forced-exception', 'detected-exception']:
                if len(re.findall(r'^EXACT ', stderr, re.M)) != 7:
                    raise ValueError('exception resolver path not reached')
            if name == 'pinning-known-hit' and hits != {'pinning_hit_0.txt': pin['expected']}:
                raise ValueError('pin replay mismatch')
            if expected == 2 and (hits or 'Done enum:' in stdout):
                raise ValueError('overflow reported completion')
            if expected == 0 and 'Done' not in stdout:
                raise ValueError('missing completion')
            results.append(dict(name=name, exit=proc.returncode, stdout=stdout, stderr=stderr, hits=hits))
            print(name, 'MEMCHECK_PASS', flush=True)
    output.write_text(json.dumps(dict(pinningSha256=PIN, subsetSha256=SUB, cases=results), indent=2)+'\n')
    print('QSB_MEMORY_PASS', hashlib.sha256(output.read_bytes()).hexdigest(), flush=True)


if __name__ == '__main__':
    main()
