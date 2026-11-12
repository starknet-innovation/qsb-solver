"""One production-sized PQB unit, through the bound worker, with durable public receipts.

    python3 run_full_unit.py BUNDLE RESULTS pinning|round0|round1

No launch, retries, smaller-unit option or timeout override. See FULL-UNIT.md.
The development reference stays in the validation bundle, outside the worker image.
"""
import base64
import hashlib
import json
import math
import os
import sys
import time
from pathlib import Path

STAGES = ('pinning', 'round0', 'round1')
RUNTIME = 'ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48'


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def write_json(path, value):
    """Replace a receipt whole and durably: file flushed, renamed, directory flushed."""
    temporary = path.with_suffix('.partial')
    with open(temporary, 'w') as stream:
        stream.write(json.dumps(value, indent=1, sort_keys=True) + '\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    directory = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def verify_bundle(bundle):
    """Check every bound input before importing bundled code; host also pins SHA256SUMS itself."""
    bundle = Path(bundle).resolve()
    seen = set()
    for line in (bundle / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = bundle / name
        if (name in seen or Path(name).is_absolute() or '..' in Path(name).parts
                or path.is_symlink() or not path.resolve().is_relative_to(bundle)
                or sha256(path) != digest):
            raise ValueError('bundle input mismatch: ' + name)
        seen.add(name)
    required = {'manifest.json', 'plan.json', 'contract.json', 'build-receipt.json', 'run_full_unit.py',
                'run_measure.py', 'reference.py', 'expected.json', 'grind-ranked',
                'worker/grind', 'worker/binding.json', 'worker/pqb_handler.py', 'worker/pqb_ranges.py'}
    if not required <= seen:
        raise ValueError('bundle checksum list is incomplete')
    if {str(p.relative_to(bundle)) for p in bundle.rglob('*') if p.is_file() and p.name != 'SHA256SUMS'} != seen:
        raise ValueError('unlisted bundle file')


def largest_units(ranges):
    """Pinning units are equal; enumerate the small round partitions to find their maxima."""
    return {stage: max(range(1 if stage == 'pinning' else ranges.unit_count(stage)),
                      key=lambda attempt: ranges.work_range(stage, attempt)['count']) for stage in STAGES}


def verify_candidate(reference, prob, stage, unit, line):
    """Independent nonce membership, gate and DER-shape checks, not a consensus verifier."""
    fields = line.split()
    if stage == 'pinning':
        seq, lt, j, rid, enc, level = map(int, fields)
        nonce = (seq - reference.PIN_SEQ_MIN) * (reference.PIN_LT_END - reference.PIN_LT_MIN) + lt - reference.PIN_LT_MIN
        if not (unit['sequence'] <= seq < unit['sequence'] + unit['sequenceCount']
                and unit['locktime'] <= lt < unit['locktime'] + unit['locktimeCount']):
            raise ValueError('pinning candidate outside unit')
    else:
        subset = tuple(map(int, fields[0].split(',')))
        j, rid, enc, level = map(int, fields[1:])
        if (len(subset) != prob['t'] or tuple(sorted(set(subset))) != subset
                or subset[0] < 0 or subset[-1] >= prob['n_slots']):
            raise ValueError('invalid candidate subset')
        nonce = reference.subset_rank(subset, prob['n_slots'])
    if not int(unit['start']) <= nonce < int(unit['start']) + unit['count']:
        raise ValueError('candidate nonce outside unit')
    if not (0 <= j < prob['K'] and 0 <= rid < prob['npts'] and 0 <= enc < prob['nenc'] and 1 <= level <= prob['H']):
        raise ValueError('candidate selector outside shape')
    if stage == 'pinning':
        digest = reference.pin_digest(prob, line)
    else:
        pre, last = bytearray(), 0
        for slot in subset:
            offset = prob['slot_offs'][slot]
            pre += prob['preimage'][last:offset]
            last = offset + prob['slot_len']
        pre += prob['preimage'][last:]
        z = int.from_bytes(reference._sha256d(bytes(pre)), 'big') % reference.N
        point = reference._add(reference._mul(z, prob['B']), prob['C'][j, rid])
        digest = reference._encodings(point, prob['nenc'])[enc]
        for _ in range(level):
            digest = hashlib.sha256(digest).digest()
    length = digest[3]
    if digest[:3] != b'\x30\x1d\x02' or not (1 <= length <= 24 and digest[4 + length] == 2 and digest[5 + length] == 25 - length):
        raise ValueError('candidate fails gate or DER shape')
    return {'candidate': line, 'nonce': str(nonce), 'digest': digest.hex()}


def run_case(bundle, results, stage, attempt, worker, reference):
    raw = (bundle / 'fixtures' / ('pin.txt' if stage == 'pinning' else stage + '.txt')).read_bytes()
    if raw.count(b'gate_bits 12\n') != 1:
        raise ValueError('unexpected fixture gate')
    raw = raw.replace(b'gate_bits 12\n', b'gate_bits 24\n')
    binding = worker.release_binding(bundle / 'worker')
    contract = json.loads((bundle / 'contract.json').read_text())
    request = {'input': {'protocol': worker.PROTOCOL, 'searchVersion': contract['searchVersion'],
                        'stage': stage, 'attempt': attempt, 'problemBase64': base64.b64encode(raw).decode(),
                        'problemSha256': hashlib.sha256(raw).hexdigest(), 'manifestHash': canonical_hash(contract),
                        'kernelCommit': binding['solverCommit']}}
    write_json(results / 'request.json', request)
    unit = worker.validate_request(request['input'], binding['solverCommit'])[1]
    begin = time.monotonic()
    response = worker.handler(request, root=bundle / 'worker', evidence_directory=results / 'work')
    worker_seconds = time.monotonic() - begin
    write_json(results / 'worker-result.json', response)     # save before independent checking
    row = {'stage': stage, 'attempt': attempt, 'workRange': unit, 'workerSeconds': worker_seconds,
           'workerResult': response, 'pass': False, 'candidateChecks': []}
    write_json(results / 'unit.json', row)
    if response['status'] != 'completed' or response['checkpoint'] != 'range-complete':
        return row
    log = (results / 'work/compute.log').read_text()
    report = worker.range_report(log, stage, unit)
    if report is None:
        raise ValueError('retained log has no exact completion report')
    row['rangeReport'] = report
    batches = [json.loads(line[7:]) for line in log.splitlines() if line.startswith('@batch ')]
    setups = [json.loads(line[7:]) for line in log.splitlines() if line.startswith('@setup ')]
    row['device'] = setups
    row['batchZblocks'] = sum(batch['z'] for batch in batches)
    # Batch timers overlap with multiple slots in flight: retain, do not sum as elapsed time.
    if row['batchZblocks'] != unit['count']:
        raise ValueError('batch accounting differs from unit')
    hits = response['candidates']
    if len(hits) != len(set(hits)):
        raise ValueError('duplicate candidate')
    prob = reference.load(results / 'work/P.txt')
    check_start = time.monotonic()
    for hit in hits:
        row['candidateChecks'].append(verify_candidate(reference, prob, stage, unit, hit))
    row['verificationSeconds'] = time.monotonic() - check_start
    mean = response['trials'] / 2 ** 24
    row['gateCountSanity'] = abs(response['gateHits'] - mean) <= 6 * math.sqrt(mean) + 6
    row['jobSeconds'] = time.monotonic() - begin
    row['pass'] = row['gateCountSanity'] and row['jobSeconds'] < worker.TIMEOUT_SECONDS
    row['nativeDevice'] = len(setups) == 1 and 'A10G' in setups[0].get('device', '')
    write_json(results / 'unit.json', row)
    return row


def run(bundle, results, stage):
    bundle, results = Path(bundle).resolve(), Path(results).resolve()
    if stage not in STAGES:
        raise ValueError('invalid stage')
    results.mkdir()                            # persistent one-shot marker before any compute
    start = time.monotonic()
    out = {'format': 'qsb-pqb-full-unit-result-v1', 'status': 'incomplete', 'stage': stage,
           'evidenceKind': 'native A10G unit validation; not a full solve or completeness proof'}
    write_json(results / 'result.json', out)
    try:
        if any(k.startswith(('QG_', 'QSB_MEASURE_')) for k in os.environ):
            raise ValueError('ambient grinder/measurement overrides are forbidden')
        verify_bundle(bundle)
        sys.path.insert(0, str(bundle / 'worker'))
        sys.path.insert(0, str(bundle))
        import pqb_handler as worker
        import pqb_ranges as ranges
        import reference
        import run_measure as measure
        manifest = json.loads((bundle / 'manifest.json').read_text())
        plan = json.loads((bundle / 'plan.json').read_text())
        binding = worker.release_binding(bundle / 'worker')
        contract = json.loads((bundle / 'contract.json').read_text())
        receipt = json.loads((bundle / 'build-receipt.json').read_text())
        if (manifest['sourceCommit'] != binding['solverCommit'] or manifest['runtimeImage'] != RUNTIME
                or manifest['contractSha256'] != canonical_hash(contract)
                or receipt['binarySha256'] != binding['files']['grind'] or receipt['cudaArchitecture'] != '86'
                or plan != {'searchVersion': ranges.VERSION, 'attempts': largest_units(ranges)}):
            raise ValueError('bundle identity or full-unit plan mismatch')
        if sha256(bundle / 'grind-ranked') != binding['files']['grind']:
            raise ValueError('preflight and worker binary differ')
        out.update(sourceCommit=manifest['sourceCommit'], binarySha256=binding['files']['grind'],
                   bundleSha256=sha256(bundle / 'SHA256SUMS'), runtimeImage=RUNTIME,
                   contractSha256=canonical_hash(json.loads((bundle / 'contract.json').read_text())),
                   workerTimeoutSeconds=worker.TIMEOUT_SECONDS)
        expected = json.loads((bundle / 'expected.json').read_text())
        measure.START, measure.DEADLINE = time.monotonic(), 60
        measure.FAILURE_DIR = results / 'preflight-failures'    # inputs and whole output of a failed case
        out['correctness'] = measure.correctness(bundle, expected)
        write_json(results / 'result.json', out)
        if not out['correctness'] or not all(c['pass'] for c in out['correctness']):
            raise ValueError('small-range correctness preflight failed; full unit not started')
        if time.monotonic() - start > 75:
            raise ValueError('preflight exceeded time allowance; full unit not started')
        out['unit'] = run_case(bundle, results, stage, plan['attempts'][stage], worker, reference)
        out['status'] = 'passed' if out['unit']['pass'] and out['unit']['nativeDevice'] else 'failed'
    except Exception as error:                 # retain failure; never automatically replay work
        out.update(status='failed', error='%s: %s' % (type(error).__name__, str(error)[:500]))
    out['elapsedSeconds'] = time.monotonic() - start
    out['files'] = {str(p.relative_to(results)): sha256(p) for p in sorted(results.rglob('*'))
                    if p.is_file() and p.name != 'result.json'}
    write_json(results / 'result.json', out)
    return out


if __name__ == '__main__':
    result = run(*sys.argv[1:])
    print(json.dumps({'status': result['status'], 'stage': result['stage']}))
    sys.exit(0 if result['status'] == 'passed' else 1)
