"""Compile isolated sm_86 variants of the subset solver and compare their SASS.

Never changes production sources or locks, never runs a solver, never needs a GPU.
"""
import difflib, hashlib, json, pathlib, shutil, subprocess
import compare_sass
from trace_source import instrument

ROOT = pathlib.Path('/src'); SRC = ROOT / 'research/optimized-subset'
HERE = ROOT / 'experiments/sha-rotate-add'; OUT = pathlib.Path('/results')
EXPERIMENT = json.loads((HERE / 'experiment-lock.json').read_text())
# The committed subset source now carries the patch. name -> (candidate source, extra compiler flags).
# The baseline is rebuilt by reversing the patch, so it stays the source the native run compared against.
VARIANTS = {
    'baseline': (False, []),
    'control': (True, ['-DQSB_SHA_LEA=0']),
    'candidate': (True, []),
    'candidate-ord0': (True, ['-DQSB_LEA_ORD=0']),
}


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def verified_flags():
    lock = json.loads((ROOT / 'worker/optimized/source-lock.json').read_text())
    actual = {str(p.relative_to(SRC)) for p in (SRC / 'subset').rglob('*') if p.is_file()}
    if actual != set(lock['files']): raise ValueError('Source inventory mismatch')
    for name, want in lock['files'].items():
        path = SRC / name
        if path.is_symlink() or sha(path) != want: raise ValueError('Source mismatch: ' + name)
    if lock['flags'].count('-arch=sm_89') != 1: raise ValueError('Unexpected locked architecture flags')
    if sha(HERE / 'sha-rotate-add.patch') != EXPERIMENT['patchSha256']: raise ValueError('Patch changed')
    if lock['files']['subset/GPUHash.h'] != EXPERIMENT['patchedGpuHashSha256']: raise ValueError('Committed source is not the candidate')
    return [f.replace('-arch=sm_89', '-arch=sm_86') for f in lock['flags']]


def compile_solver(name, work, flags):
    binary = OUT / name
    command = ['nvcc', *flags, '-Xptxas=-v', '-o', str(binary), str(work / 'subset/subset.cu'), '-lcrypto', '-lm']
    with (OUT / (name + '.log')).open('w') as log:
        done = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=600)
    if done.returncode:
        print((OUT / (name + '.log')).read_text()[-6000:])
        raise SystemExit(f'{name}: nvcc exited {done.returncode}')
    return binary


def build_trace(flags, records):
    """Diagnostic derivative of the candidate. The unmodified candidate above stays the binary under test."""
    work = pathlib.Path('/tmp/candidate-trace'); shutil.copytree(pathlib.Path('/tmp/candidate'), work)
    tree = work / 'subset/tests/gpu_epochs/tree.cu'
    original = tree.read_text(); changed = instrument(original); tree.write_text(changed)
    (OUT / 'candidate-trace.diff').write_text(''.join(difflib.unified_diff(
        original.splitlines(True), changed.splitlines(True), fromfile='candidate/tree.cu', tofile='trace/tree.cu')))
    compile_solver('candidate-trace', work, flags)
    (OUT / 'trace-receipt.json').write_text(json.dumps(dict(
        unmodifiedBinarySha256=records['candidate']['binarySha256'],
        unmodifiedTreeSha256=hashlib.sha256(original.encode()).hexdigest(),
        unmodifiedGpuHashSha256=records['candidate']['gpuHashSha256'],
        diagnosticTreeSha256=hashlib.sha256(changed.encode()).hexdigest(), flags=flags,
        files={name: sha(OUT / name) for name in ['candidate-trace', 'candidate-trace.diff']},
        status='UNEXECUTED', cpuVerified=False,
        scope='Diagnostic derivative; does not attest execution of the unmodified binary'), indent=2) + '\n')


def main():
    flags = verified_flags(); OUT.mkdir(exist_ok=False); records = {}
    for name, (patched, extra) in VARIANTS.items():
        work = pathlib.Path('/tmp') / name; shutil.copytree(SRC, work)
        if not patched:
            subprocess.run(['patch', '--batch', '-R', '-p1', '-i', str(HERE / 'sha-rotate-add.patch')], cwd=work, check=True)
        expected = EXPERIMENT['patchedGpuHashSha256' if patched else 'baselineGpuHashSha256']
        if sha(work / 'subset/GPUHash.h') != expected: raise ValueError('Variant source mismatch: ' + name)
        binary = compile_solver(name, work, [*flags, *extra])
        with (OUT / (name + '.sass')).open('w') as sass:
            subprocess.run(['cuobjdump', '-sass', str(binary)], stdout=sass, check=True, timeout=300)
        records[name] = {'binarySha256': sha(binary), 'gpuHashSha256': sha(work / 'subset/GPUHash.h'),
                         'flags': [*flags, *extra], 'patched': patched}
    build_trace(flags, records)
    # The frozen pair handed to a native run: small enough for the bounded staging download.
    pair = OUT / 'pair'; pair.mkdir()
    for name in ['baseline', 'candidate', 'candidate-trace', 'candidate-trace.diff', 'trace-receipt.json']:
        shutil.copy2(OUT / name, pair / name)
    baseline = compare_sass.summarise((OUT / 'baseline.sass').read_text())
    report = {'scope': 'Static instruction counts. Not a timing or correctness result.', 'baseline': baseline, 'variants': {}}
    for name in VARIANTS:
        if name == 'baseline': continue
        summary = compare_sass.summarise((OUT / (name + '.sass')).read_text())
        report['variants'][name] = {'summary': summary, 'delta': compare_sass.compare(baseline, summary)}
    (OUT / 'sass-comparison.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    (OUT / 'build.json').write_text(json.dumps({
        'experiment': EXPERIMENT, 'variants': records,
        'pair': {name: sha(OUT / 'pair' / name) for name in sorted(p.name for p in (OUT / 'pair').iterdir())},
        'compiler': subprocess.check_output(['nvcc', '--version'], text=True),
        'packages': subprocess.check_output(['dpkg-query', '-W', 'gcc', 'g++', 'libssl-dev'], text=True),
        'controlMatchesBaseline': report['variants']['control']['delta']['identicalSass'],
        'gpuExecuted': False, 'status': 'UNEXECUTED',
        'scope': 'Compile-only comparison. No solver was run; no correctness or performance is established.',
    }, indent=2, sort_keys=True) + '\n')
    summary = {name: {k: v['delta'][k] for k in ('identicalSass', 'instructions', 'leaInstructions')}
               for name, v in report['variants'].items()}
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
