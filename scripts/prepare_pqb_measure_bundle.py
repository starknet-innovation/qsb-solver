"""Assemble the hash-verified bundle for a native PQB measurement run. Launches nothing.

    python3 scripts/prepare_pqb_measure_bundle.py BINARIES_DIR OUT_DIR

BINARIES_DIR is the `pqb-measure-binaries-sm86` CI artifact of the commit being measured:
grind-ranked, grind-upstream, build-receipt.json, source-commit, source-event, and a SHA256SUMS
that lists all five. Use the artifact of
the push run: source-commit is the commit CI checked out and built, which on a pull_request run
is the merge commit and never equals a branch checkout. The checkout must be
clean and at that commit, so the fixtures, expected hit sets and runner are the committed ones.
"""
import hashlib
import json
import pathlib
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MEASURE = ROOT / 'research/pqb-ranked/measure'
FIXTURES = ROOT / 'research/pqb-ranked/tests/fixtures'
BINARIES = ('grind-ranked', 'grind-upstream')


def sha256(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def git(*args):
    return subprocess.run(['git', '-C', str(ROOT)] + list(args), check=True, capture_output=True, text=True).stdout.strip()


def prepare(binaries, out, commit=None):
    binaries, out = pathlib.Path(binaries), pathlib.Path(out)
    sums = dict(reversed(line.split()) for line in (binaries / 'SHA256SUMS').read_text().splitlines())
    # The source identity files are checked like the binaries: an artifact whose commit or event
    # file was swapped, or mixed in from another download, must not pass.
    listed = BINARIES + ('build-receipt.json', 'source-commit', 'source-event')
    if sorted(sums) != sorted(listed):
        raise SystemExit('artifact SHA256SUMS must list exactly: ' + ', '.join(sorted(listed)))
    for name in listed:
        if sha256(binaries / name) != sums[name]:
            raise SystemExit('artifact file differs from its SHA256SUMS: ' + name)
    receipt = json.loads((binaries / 'build-receipt.json').read_text())
    if receipt.get('binarySha256') != sums['grind-ranked'] or receipt.get('status') != 'HOLD':
        raise SystemExit('build receipt does not describe grind-ranked')
    # A pull_request run builds a synthetic merge commit that was never pushed as a branch tip. Even
    # with that commit checked out, native work must come from a push run of a pushed commit.
    if (binaries / 'source-event').read_text().strip() != 'push':
        raise SystemExit('native measurement requires the push workflow artifact, not a pull_request one')
    built = (binaries / 'source-commit').read_text().strip()
    if commit is None:
        if git('status', '--porcelain'):
            raise SystemExit('checkout is not clean')
        commit = git('rev-parse', 'HEAD')
    if built != commit:
        raise SystemExit('binaries were built from %s, the checkout is at %s (a pull_request run builds the '
                         'merge commit: use the push run\'s artifact)' % (built, commit))
    lock = json.loads((ROOT / 'research/pqb-ranked/source-lock.json').read_text())
    if receipt['sourceLock'] != lock:
        raise SystemExit('binaries were built from a different source lock')
    expected = json.loads((MEASURE / 'expected.json').read_text())
    out.mkdir(parents=True)
    (out / 'fixtures').mkdir()
    for name in BINARIES:
        shutil.copy(binaries / name, out / name)
        (out / name).chmod(0o555)
    shutil.copy(binaries / 'build-receipt.json', out / 'build-receipt.json')
    for name, digest in expected['fixtures'].items():
        if sha256(FIXTURES / name) != digest:
            raise SystemExit('fixture differs from expected.json: ' + name)
        shutil.copy(FIXTURES / name, out / 'fixtures' / name)
    shutil.copy(MEASURE / 'expected.json', out / 'expected.json')
    shutil.copy(MEASURE / 'run_measure.py', out / 'run_measure.py')
    manifest = {'format': 'qsb-pqb-measure-bundle-v1', 'sourceCommit': commit,
                'sourceEvent': (binaries / 'source-event').read_text().strip(),
                'binaries': {name: sums[name] for name in BINARIES},
                'note': 'CI build artifacts, not attested release binaries. Public synthetic inputs only.'}
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=1, sort_keys=True) + '\n')
    files = sorted(p for p in out.rglob('*') if p.is_file())
    (out / 'SHA256SUMS').write_text(''.join('%s  %s\n' % (sha256(p), p.relative_to(out)) for p in files))
    return sha256(out / 'SHA256SUMS')


if __name__ == '__main__':
    print(prepare(sys.argv[1], sys.argv[2]))
