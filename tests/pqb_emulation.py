"""Build the adapted PQB grinder as plain C++ (-DQG_EMU) for tests. No GPU, no CUDA toolkit.

The emulation build runs the same kernel source on the CPU. It exercises the range walk, the
hashing and the curve arithmetic as written; it says nothing about a CUDA build's code generation,
device execution or speed.
"""
import hashlib
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'research/pqb-ranked/grind.cu'
INCLUDE = ROOT / 'vendor/pqb/grinder'
FIXTURES = ROOT / 'research/pqb-ranked/tests/fixtures'
UPSTREAM = INCLUDE / 'grind.cu'


def compiler():
    return shutil.which('c++') or shutil.which('g++') or shutil.which('clang++')


def build(source=SOURCE):
    """Path of the emulation binary, compiled once per source identity; None without a compiler."""
    cxx = compiler()
    if not cxx:
        return None
    digest = hashlib.sha256()
    for file in (source, INCLUDE / 'common.cuh', INCLUDE / 'ptx_field.cuh'):
        digest.update(file.read_bytes())
    out = Path(tempfile.gettempdir()) / ('qsb-pqb-emu-%s-%d' % (digest.hexdigest()[:16], os.getuid()))
    binary = out / 'grind'
    if not binary.is_file():
        out.mkdir(mode=0o700, exist_ok=True)
        partial = out / ('grind.%d' % os.getpid())
        subprocess.run([cxx, '-O2', '-std=c++17', '-DQG_EMU', '-x', 'c++', '-I', str(INCLUDE),
                        str(source), '-o', str(partial), '-lpthread'], check=True)
        os.replace(partial, binary)
    return binary


def problem(name, gate_bits=None):
    """A fixture problem's bytes, optionally at another gate width."""
    raw = (FIXTURES / (name + '.txt')).read_bytes()
    if gate_bits is not None:
        assert raw.count(b'gate_bits 12\n') == 1
        raw = raw.replace(b'gate_bits 12\n', b'gate_bits %d\n' % gate_bits)
    return raw


def run(binary, raw, args, env=None):
    """Run the grinder on problem bytes. Returns (returncode, stdout + stderr, sorted hit lines)."""
    with tempfile.TemporaryDirectory(prefix='qsb-pqb-test-') as d:
        (Path(d) / 'P.txt').write_bytes(raw)
        done = subprocess.run([str(binary), '--problem', 'P.json', '--hits', 'hits.txt'] + [str(a) for a in args],
                              cwd=d, capture_output=True, text=True, timeout=600,
                              env=dict(os.environ, **(env or {})))
        hits = Path(d) / 'hits.txt'
        lines = sorted(ln for ln in hits.read_text().split('\n') if ln) if hits.is_file() else []
    return done.returncode, done.stdout + done.stderr, lines
