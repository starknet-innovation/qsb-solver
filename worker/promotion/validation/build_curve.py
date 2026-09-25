"""Compile a diagnostic audit from exactly the optimized source lock and flags."""
import hashlib
import json
from pathlib import Path
import subprocess
from curve_vectors import scalars, encode


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    root = Path('/src')
    lockfile = root / 'worker/optimized/source-lock.json'
    lock = json.loads(lockfile.read_text())
    source = root / 'research/optimized-subset'
    actual = {str(p.relative_to(source)): sha(p) for p in (source/'subset').rglob('*') if p.is_file()}
    if actual != lock['files']:
        raise ValueError('audit source differs from candidate source lock')
    output = Path('/opt/qsb-curve-audit')
    output.mkdir()
    vectors = output/'vectors.bin'
    vectors.write_bytes(encode(scalars()))
    executable = output/'point-audit'
    command = ['nvcc', *lock['flags'], '-o', str(executable),
               str(source/'subset/tests/gpu_epochs/point_audit.cu'), '-lcrypto', '-lm']
    subprocess.run(command, check=True)
    receipt = dict(sourceLockSha256=sha(lockfile), sourceFiles=actual, flags=lock['flags'],
                   compiler=subprocess.check_output(['nvcc', '--version'], text=True),
                   files={p.name:sha(p) for p in [vectors, executable]}, scalarCount=len(scalars()),
                   scope='Diagnostic compiled from candidate source and flags; not the shipped solver binary',
                   status='UNEXECUTED')
    (output/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')


if __name__ == '__main__':
    main()
