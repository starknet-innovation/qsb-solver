"""Qualify one production unit through the installed final image, retaining all public work.

Mount the verified public gate at /gate and a fresh results parent at /results.
The verifier/reference and fixtures stay outside the image; worker code is imported
only from /opt/qsb-pqb. No provider, wallet, signing or publication code.
"""
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import hashlib


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as file:
        for data in iter(lambda:file.read(1024*1024),b''):
            digest.update(data)
    return digest.hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def verify_gate(gate):
    rows = {}
    for line in (gate/'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = gate/name
        if (name in rows or Path(name).is_absolute() or '..' in Path(name).parts
                or path.is_symlink() or not path.resolve().is_relative_to(gate)
                or sha(path) != digest):
            raise ValueError('Invalid public gate input: '+name)
        rows[name] = digest
    actual = {str(p.relative_to(gate)) for p in gate.rglob('*') if p.is_file() and p.name != 'SHA256SUMS'}
    if actual != set(rows) or not {'qualify_image.py','run_full_unit.py','run_measure.py','reference.py',
                                  'expected.json','binding.json','contract.json','oci-identity.json'} <= set(rows):
        raise ValueError('Incomplete public gate inventory')


def run(gate, result, stage):
    gate, result = Path(gate).resolve(), Path(result).resolve()
    result.mkdir()  # one-shot marker before importing code or executing native work
    # Import the durable receipt helper only after checking its external gate hashes.
    verify_gate(gate)
    full = load('full_unit_reference', gate/'run_full_unit.py')
    out = dict(format='qsb-pqb-final-image-qualification-v1', status='incomplete', stage=stage,
               gateSha256=sha(gate/'SHA256SUMS'), scope='Installed final image; synthetic native cases and one largest unit')
    full.write_json(result/'result.json', out)
    started = time.monotonic()
    try:
        if stage not in full.STAGES or any(k.startswith(('QG_','QSB_MEASURE_')) for k in os.environ):
            raise ValueError('Invalid stage or ambient experimental overrides')
        identity = json.loads((gate/'oci-identity.json').read_text())
        expected_binding = json.loads((gate/'binding.json').read_text())
        installed = Path('/opt/qsb-pqb')
        sys.path.insert(0, str(installed))
        worker = load('installed_pqb_handler', installed/'pqb_handler.py')
        ranges = load('installed_pqb_ranges', installed/'pqb_ranges.py')
        binding = worker.release_binding(installed)
        if binding != expected_binding:
            raise ValueError('Installed image binding differs from verified build artifact')
        receipt = json.loads((installed/'build-receipt.json').read_text())
        if receipt['binarySha256'] != binding['files']['grind'] or receipt['cudaArchitecture'] != '86':
            raise ValueError('Installed compiler/binary identity differs')
        contract = json.loads((gate/'contract.json').read_text())
        for vector in contract['cases']:
            if ranges.work_range(vector['stage'],vector['attempt']) != vector['range']:
                raise ValueError('Installed partition differs from contract')
        for vector in contract['invalid']:
            try:
                ranges.work_range(vector['stage'],vector['attempt'])
            except ValueError:
                continue
            raise ValueError('Installed partition accepts an invalid vector')
        reference = load('independent_public_reference', gate/'reference.py')
        measure = load('native_small_cases', gate/'run_measure.py')
        out.update(image=identity, binding=binding, buildReceipt=receipt,
                   contractSha256=full.canonical_hash(contract),workerTimeoutSeconds=worker.TIMEOUT_SECONDS)
        full.write_json(result/'result.json', out)
        with tempfile.TemporaryDirectory(prefix='pqb-final-image-') as temporary:
            bundle = Path(temporary)
            for name, target in [('worker',installed),('grind-ranked',installed/'grind'),
                                 ('fixtures',gate/'fixtures'),('contract.json',gate/'contract.json')]:
                (bundle/name).symlink_to(target)
            expected = json.loads((gate/'expected.json').read_text())
            for name, digest in expected['fixtures'].items():
                if sha(gate/'fixtures'/name) != digest:
                    raise ValueError('Independent fixture differs from its expected hit-set identity')
            original_run = measure.run
            count = 0
            def retained_run(binary, problem, args, env=None, timeout=120):
                nonlocal count
                record = result/'small-cases'/('%02d'%count)
                count += 1
                record.mkdir(parents=True)
                (record/'P.txt').write_bytes(problem)
                full.write_json(record/'invocation.json',dict(args=args,env=env or {},binarySha256=sha(binary)))
                measure.LAST = None
                try:
                    return original_run(binary,problem,args,env,timeout)
                finally:
                    if measure.LAST is not None:
                        for name, value in zip(('stdout.txt','stderr.txt','hits.txt'),measure.LAST[-3:]):
                            (record/name).write_text(value)
            measure.run = retained_run
            measure.START, measure.DEADLINE = time.monotonic(), 60
            measure.FAILURE_DIR = result/'preflight-failures'
            out['correctness'] = measure.correctness(bundle, expected)
            full.write_json(result/'result.json', out)
            if not out['correctness'] or not all(row['pass'] for row in out['correctness']):
                raise ValueError('Native correctness failed; full unit not started')
            if time.monotonic()-started > 75:
                raise ValueError('Preflight exceeded its allowance; full unit not started')
            out['unit'] = full.run_case(bundle,result,stage,full.largest_units(ranges)[stage],worker,reference)
            out['status'] = 'passed' if out['unit']['pass'] and out['unit']['nativeDevice'] else 'failed'
    except Exception as error:
        out.update(status='failed',error=type(error).__name__+': '+str(error)[:500])
    out['elapsedSeconds'] = time.monotonic()-started
    out['files'] = {str(p.relative_to(result)):sha(p) for p in sorted(result.rglob('*')) if p.is_file() and p.name!='result.json'}
    full.write_json(result/'result.json',out)
    return out


if __name__ == '__main__':
    result = run(*sys.argv[1:])
    print(json.dumps(dict(status=result['status'],stage=result['stage'])))
    raise SystemExit(0 if result['status']=='passed' else 1)
