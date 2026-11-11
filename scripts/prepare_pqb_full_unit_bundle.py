"""Prepare a full-unit validation bundle from this clean, pushed commit's CI artifact.

    python3 scripts/prepare_pqb_full_unit_bundle.py BINARIES_DIR OUT_DIR

No cloud calls or launches. The artifact is pqb-measure-binaries-sm86 from a push run.
"""
import importlib.util
import json
import shutil
import sys
from pathlib import Path

import prepare_pqb_measure_bundle as measurement

ROOT = Path(__file__).resolve().parents[1]


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    loaded = importlib.util.module_from_spec(spec)
    saved = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        spec.loader.exec_module(loaded)
    finally:
        sys.dont_write_bytecode = saved
    return loaded


def prepare(binaries, out):
    commit = measurement.git('rev-parse', 'HEAD')
    if measurement.git('status', '--porcelain'):
        raise SystemExit('checkout is not clean')
    # Local remote-tracking refs alone can be stale. Require a live, exact pushed branch tip.
    remote = measurement.git('ls-remote', '--heads', 'origin')
    if not any(line.split()[0] == commit for line in remote.splitlines()):
        raise SystemExit('HEAD must be pushed as a branch tip before preparing native work')
    lock = json.loads((ROOT / 'research/pqb-ranked/source-lock.json').read_text())
    for name, digest in lock['sources'].items():
        if measurement.sha256(ROOT / name) != digest:
            raise SystemExit('source differs from lock: ' + name)
    receipt = json.loads((Path(binaries) / 'build-receipt.json').read_text())
    if (Path(binaries) / 'source-event').read_text().strip() != 'push':
        raise SystemExit('full-unit validation requires the push workflow artifact')
    if receipt.get('format') != 'qsb-pqb-build-receipt-v1' or receipt.get('cudaArchitecture') != '86':
        raise SystemExit('full-unit validation requires the native sm86 CI receipt')
    measurement.prepare(binaries, out)           # clean source identity, artifact hashes, lock, fixtures
    out = Path(out)
    worker = out / 'worker'
    worker.mkdir()
    shutil.copy(out / 'grind-ranked', worker / 'grind')
    for name in ('pqb_handler.py', 'pqb_ranges.py'):
        shutil.copy(ROOT / 'worker/pqb' / name, worker / name)
    binding = {'format': 'qsb-pqb-candidate-v1', 'status': 'HOLD', 'solverCommit': commit,
               'cudaArchitecture': '86', 'files': {name: measurement.sha256(worker / name)
                                                  for name in ('grind', 'pqb_handler.py', 'pqb_ranges.py')}}
    (worker / 'binding.json').write_text(json.dumps(binding, indent=1, sort_keys=True) + '\n')
    shutil.copy(ROOT / 'contracts/pqb-ranked-v2.json', out / 'contract.json')
    shutil.copy(ROOT / 'research/pqb-ranked/tests/reference.py', out / 'reference.py')
    shutil.copy(ROOT / 'research/pqb-ranked/measure/run_full_unit.py', out / 'run_full_unit.py')
    runner = module('pqb_full_unit_plan', out / 'run_full_unit.py')
    ranges = module('pqb_full_unit_ranges', worker / 'pqb_ranges.py')
    contract = json.loads((out / 'contract.json').read_text())
    for vector in contract['cases']:
        if ranges.work_range(vector['stage'], vector['attempt']) != vector['range']:
            raise SystemExit('contract vector differs from scheduler')
    for vector in contract['invalid']:
        try:
            ranges.work_range(vector['stage'], vector['attempt'])
        except ValueError:
            continue
        raise SystemExit('scheduler accepts invalid contract vector')
    runner.write_json(out / 'plan.json', {'searchVersion': ranges.VERSION, 'attempts': runner.largest_units(ranges)})
    manifest = json.loads((out / 'manifest.json').read_text())
    manifest.update(format='qsb-pqb-full-unit-bundle-v1', runtimeImage=runner.RUNTIME,
                    contractSha256=runner.canonical_hash(contract),
                    note='HOLD. CI binaries, not attested releases. Validation reference outside worker image.')
    runner.write_json(out / 'manifest.json', manifest)
    files = sorted(p for p in out.rglob('*') if p.is_file() and p.name != 'SHA256SUMS')
    (out / 'SHA256SUMS').write_text(''.join('%s  %s\n' % (measurement.sha256(p), p.relative_to(out)) for p in files))
    return measurement.sha256(out / 'SHA256SUMS')


if __name__ == '__main__':
    print(prepare(*sys.argv[1:]))
