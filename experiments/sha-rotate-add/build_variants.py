"""Compile isolated sm_86 variants of the subset solver and compare their SASS.

Never changes production sources or locks, never runs a solver, never needs a GPU.
"""
import hashlib, json, pathlib, shutil, subprocess
import compare_sass

ROOT = pathlib.Path('/src'); SRC = ROOT / 'research/optimized-subset'
HERE = ROOT / 'experiments/sha-rotate-add'; OUT = pathlib.Path('/results')
EXPERIMENT = json.loads((HERE / 'experiment-lock.json').read_text())
# name -> (apply patch, extra compiler flags)
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
    if lock['files']['subset/GPUHash.h'] != EXPERIMENT['baselineGpuHashSha256']: raise ValueError('Baseline changed')
    return [f.replace('-arch=sm_89', '-arch=sm_86') for f in lock['flags']]


def main():
    flags = verified_flags(); OUT.mkdir(exist_ok=False); records = {}
    for name, (patched, extra) in VARIANTS.items():
        work = pathlib.Path('/tmp') / name; shutil.copytree(SRC, work)
        if patched:
            subprocess.run(['patch', '--batch', '-p1', '-i', str(HERE / 'sha-rotate-add.patch')], cwd=work, check=True)
            if sha(work / 'subset/GPUHash.h') != EXPERIMENT['patchedGpuHashSha256']: raise ValueError('Patched source mismatch')
        binary = OUT / name
        command = ['nvcc', *flags, *extra, '-Xptxas=-v', '-o', str(binary), str(work / 'subset/subset.cu'), '-lcrypto', '-lm']
        with (OUT / (name + '.log')).open('w') as log:
            done = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        if done.returncode:
            print((OUT / (name + '.log')).read_text()[-6000:])
            raise SystemExit(f'{name}: nvcc exited {done.returncode}')
        with (OUT / (name + '.sass')).open('w') as sass:
            subprocess.run(['cuobjdump', '-sass', str(binary)], stdout=sass, check=True, timeout=300)
        records[name] = {'binarySha256': sha(binary), 'gpuHashSha256': sha(work / 'subset/GPUHash.h'),
                         'flags': [*flags, *extra], 'patched': patched}
    baseline = compare_sass.summarise((OUT / 'baseline.sass').read_text())
    report = {'scope': 'Static instruction counts. Not a timing or correctness result.', 'baseline': baseline, 'variants': {}}
    for name in VARIANTS:
        if name == 'baseline': continue
        summary = compare_sass.summarise((OUT / (name + '.sass')).read_text())
        report['variants'][name] = {'summary': summary, 'delta': compare_sass.compare(baseline, summary)}
    (OUT / 'sass-comparison.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    (OUT / 'build.json').write_text(json.dumps({
        'experiment': EXPERIMENT, 'variants': records,
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
