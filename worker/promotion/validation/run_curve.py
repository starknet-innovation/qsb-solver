"""Run a hash-bound diagnostic and require every planned point to be checked."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def validate_output(output, scalar_count):
    matches = re.findall(r'Point GPU audit PASS: chunks=(\d+) input_cases=(\d+) point_cases=(\d+) infinity_cases=(\d+) table_checks=(\d+) errors=(\d+)', output)
    if len(matches) != 1:
        raise ValueError('missing or duplicate final point audit verdict')
    chunks, inputs, points, infinity, tables, errors = map(int, matches[0])
    if inputs != scalar_count or points != 2*scalar_count or errors or infinity < 4 or tables != 2*(chunks*4+192):
        raise ValueError('incomplete or failing point audit')
    return dict(inputCases=inputs, pointCases=points, infinityCases=infinity,
                tableChecks=tables, errors=errors, chunks=chunks)


def main():
    root = Path(sys.argv[1]).resolve()
    receipt_file = root/'receipt.json'
    if hashlib.sha256(receipt_file.read_bytes()).hexdigest() != sys.argv[2]:
        raise ValueError('receipt identity mismatch')
    receipt = json.loads(receipt_file.read_text())
    if set(receipt['files']) != {'point-audit', 'vectors.bin'}:
        raise ValueError('unexpected artifact set')
    for name, expected in receipt['files'].items():
        path = root/name
        if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('artifact identity mismatch')
    executable = root/'point-audit'
    executable.chmod(0o700)
    result = subprocess.run([str(executable), str(root/'vectors.bin')],
                            capture_output=True, text=True, timeout=180)
    print(result.stdout, end='')
    if result.returncode:
        raise RuntimeError(f'audit failed {result.returncode}: {result.stderr[-2000:]}')
    verdict = validate_output(result.stdout, receipt['scalarCount'])
    print(json.dumps(dict(verdict=verdict, receiptSha256=sys.argv[2], scope=receipt['scope'])))


if __name__ == '__main__':
    main()
