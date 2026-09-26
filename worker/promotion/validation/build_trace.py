"""Compile a trace-only copy of the locked kernel; never replace the solver artifact."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import difflib


def checked_flags(lock, build, lock_sha):
    architecture = build.get('architecture')
    if architecture not in ('sm_86', 'sm_89'):
        raise ValueError('unsupported trace architecture')
    flags = lock['flags']
    if flags.count('-arch=sm_89') != 1:
        raise ValueError('unexpected locked architecture')
    expected = [f'-arch={architecture}' if f == '-arch=sm_89' else f for f in flags]
    if build.get('flags') != expected or build.get('sourceLockSha256') != lock_sha:
        raise ValueError('trace build differs from unmodified build flags/source lock')
    return expected


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    root = Path('/src')
    lockfile = root/'worker/optimized/source-lock.json'
    lock = json.loads(lockfile.read_text())
    source = root/'research/optimized-subset'
    actual = {str(p.relative_to(source)): sha(p) for p in (source/'subset').rglob('*') if p.is_file()}
    if actual != lock['files']:
        raise ValueError('trace source differs from candidate source lock')
    build = json.loads(Path('/opt/qsb-validation/build-receipt.json').read_text())
    flags = checked_flags(lock, build, sha(lockfile))
    traced = Path('/tmp/qsb-trace')
    shutil.copytree(source, traced)
    tree = traced/'subset/tests/gpu_epochs/tree.cu'
    original = tree.read_text()
    anchor = '        int vv;'
    if original.count(anchor) != 1:
        raise ValueError('trace anchor changed')
    trace = '        printf("TRACE_SUB indices=%d,%d,%d,%d,%d,%d,%d,%d,%d recid=%d hash=%08x%08x%08x%08x%08x%08x%08x%08x\\n",skip[0],skip[1],skip[2],skip[3],skip[4],skip[5],skip[6],skip[7],skip[8],ri,hs[0],hs[1],hs[2],hs[3],hs[4],hs[5],hs[6],hs[7]);\n'
    changed = original.replace(anchor, trace+anchor)
    tree.write_text(changed)
    output = Path('/opt/qsb-trace-audit'); output.mkdir()
    patch = output/'trace.diff'
    patch.write_text(''.join(difflib.unified_diff(original.splitlines(True),changed.splitlines(True),fromfile='locked/tree.cu',tofile='diagnostic/tree.cu')))
    executable = output/'trace-subset'
    subprocess.run(['nvcc', *flags, '-o', str(executable),str(traced/'subset/subset.cu'),'-lcrypto','-lm'],check=True)
    receipt = dict(sourceLockSha256=sha(lockfile),sourceFiles=actual,flags=flags,architecture=build['architecture'],
                   compiler=subprocess.check_output(['nvcc','--version'],text=True),
                   unmodifiedBinarySha256=build['binarySha256'],
                   files={p.name:sha(p) for p in [executable,patch]},
                   scope='Trace-only derivative with unchanged predicates; not final binary coverage attestation',status='UNEXECUTED')
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__ == '__main__':
    main()
