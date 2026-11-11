"""Compile the adapted PQB grinder from exactly the locked sources and write a build receipt."""
import hashlib
import json
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = pathlib.Path('/opt/qsb-pqb')


def sha256(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def main():
    arch = os.environ.get('CUDA_ARCH', '')
    if arch not in ('86', '89'):
        sys.exit('CUDA_ARCH must be 86 or 89')
    lock = json.loads((ROOT / 'research/pqb-ranked/source-lock.json').read_text())
    if lock.get('format') != 'qsb-pqb-ranked-source-lock-v1' or lock.get('status') != 'HOLD':
        sys.exit('unexpected source lock')
    for name, expected in lock['sources'].items():
        if sha256(ROOT / name) != expected:
            sys.exit('source differs from the lock: ' + name)
    present = {p.name for p in (ROOT / 'vendor/pqb/grinder').iterdir()} | {'grind.cu'}
    if present != {'grind.cu', 'common.cuh', 'ptx_field.cuh', 'README.md'}:
        sys.exit('unexpected grinder files')
    flags = ['-O3', '-std=c++17', '-arch=sm_' + arch, '-I', str(ROOT / 'vendor/pqb/grinder')]
    OUT.mkdir(parents=True, exist_ok=True)
    binary = OUT / 'grind'
    subprocess.run(['nvcc'] + flags + ['-o', str(binary), str(ROOT / 'research/pqb-ranked/grind.cu')], check=True)
    version = subprocess.run(['nvcc', '--version'], check=True, capture_output=True, text=True).stdout
    receipt = {'format': 'qsb-pqb-build-receipt-v1', 'status': 'HOLD', 'cudaArchitecture': arch,
               'compiler': version.strip().splitlines(), 'flags': flags, 'sourceLock': lock,
               'sourceLockSha256': sha256(ROOT / 'research/pqb-ranked/source-lock.json'),
               'binarySha256': sha256(binary),
               'note': 'Compiled, not executed. No native correctness or performance evidence is implied.'}
    (OUT / 'build-receipt.json').write_text(json.dumps(receipt, indent=1, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
