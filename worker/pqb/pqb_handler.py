"""PQB candidate worker: one ranked unit of one stage per request, public data only.

The request carries the grinder's public problem (pqb's `P.txt`: the legacy-sighash preimage, the
menu as curve points and B = -r^-1 G). No seed, preimage secret, menu scalar or key is accepted,
and unknown fields are refused. The result lists untrusted candidates; the consumer re-derives
each one and runs the full solve check itself. `range-complete` is this worker's statement about
its own run, not proof that nothing was missed.
"""
import base64
import hashlib
import json
import os
import pathlib
import re
import signal
import subprocess
import tempfile
import time

from pqb_ranges import ROUNDS, VERSION, work_range

ROOT = pathlib.Path(__file__).resolve().parent
PROTOCOL = 'pqb-v1'
GATE_BITS, GATE_TAG = 24, 0x301D0200            # 30 1D 02: the fixed prefix of a 32-byte signature
SHAPES = {'pinning': {'kind': 'pin', 'K': 12, 'npts': 2, 'nenc': 3, 'H': 1},
          'round0': {'kind': 'round', 'K': 16, 'npts': 4, 'nenc': 3, 'H': 1},
          'round1': {'kind': 'round', 'K': 16, 'npts': 4, 'nenc': 1, 'H': 1}}
REQUIRED = {'grind', 'pqb_handler.py', 'pqb_ranges.py'}
MAX_PROBLEM = 100000
MAX_CANDIDATES = 32
TIMEOUT_SECONDS = 840                          # under a 900-second job limit, so a slow unit ends as 'interrupted'
_INT_KEYS = {'gate_bits', 'gate_tag', 'K', 'npts', 'nenc', 'H', 'preimage_len', 'seq_off',
             'lt_off', 't', 'n_slots', 'slot_len'}
_HEX64 = re.compile('[0-9a-f]{64}')
_UINT = re.compile('0|[1-9][0-9]{0,9}')


def release_binding(root=ROOT):
    binding = json.loads((root / 'binding.json').read_bytes())
    if (binding.get('format') != 'qsb-pqb-candidate-v1' or binding.get('status') != 'HOLD'
            or not re.fullmatch('[a-f0-9]{40}', binding.get('solverCommit', ''))
            or set(binding.get('files', {})) != REQUIRED):
        raise ValueError('Invalid PQB release binding')
    for name, expected in binding['files'].items():
        file = root / name
        if file.is_symlink() or hashlib.sha256(file.read_bytes()).hexdigest() != expected:
            raise ValueError('Installed PQB artifact mismatch: ' + name)
    return binding


def parse_problem(raw, stage):
    """Check a problem file line by line against the stage's shape. Returns its integer fields."""
    try:
        text = raw.decode('ascii')
    except UnicodeDecodeError:
        raise ValueError('Problem is not ASCII') from None
    if not text.endswith('\n'):
        raise ValueError('Problem must end with a newline')
    fields, slots, points, seen = {}, [], set(), set()
    preimage = None
    for line in text[:-1].split('\n'):
        parts = line.split(' ')
        key = parts[0]
        if key in ('track', 'kind'):
            if len(parts) != 2 or key in fields or not re.fullmatch('[a-z0-9]{1,16}', parts[1]):
                raise ValueError('Invalid problem line')
            fields[key] = parts[1]
        elif key in _INT_KEYS:
            if len(parts) != 2 or key in fields or not _UINT.fullmatch(parts[1]):
                raise ValueError('Invalid problem line')
            fields[key] = int(parts[1])
        elif key == 'slot':
            if len(parts) != 3 or parts[1] != str(len(slots)) or not _UINT.fullmatch(parts[2]):
                raise ValueError('Invalid slot line')
            slots.append(int(parts[2]))
        elif key == 'B':
            if len(parts) != 3 or 'B' in seen or not all(_HEX64.fullmatch(p) for p in parts[1:]):
                raise ValueError('Invalid B line')
            seen.add('B')
        elif key == 'C':
            if (len(parts) != 5 or not _UINT.fullmatch(parts[1]) or not _UINT.fullmatch(parts[2])
                    or not all(_HEX64.fullmatch(p) for p in parts[3:])):
                raise ValueError('Invalid C line')
            point = (int(parts[1]), int(parts[2]))
            if point in points:
                raise ValueError('Duplicate menu point')
            points.add(point)
        elif key == 'preimage':
            if len(parts) != 2 or preimage is not None or not re.fullmatch('([0-9a-f]{2})+', parts[1]):
                raise ValueError('Invalid preimage line')
            preimage = parts[1]
        else:
            raise ValueError('Unknown problem field')
    shape = SHAPES[stage]
    if any(fields.get(k) != v for k, v in shape.items()):
        raise ValueError('Problem does not have the stage shape')
    if fields.get('gate_bits') != GATE_BITS or fields.get('gate_tag') != GATE_TAG:
        raise ValueError('Problem gate is not the contract gate')
    if 'B' not in seen or points != {(j, r) for j in range(shape['K']) for r in range(shape['npts'])}:
        raise ValueError('Problem menu is incomplete')
    if preimage is None or fields.get('preimage_len') != len(preimage) // 2:
        raise ValueError('Preimage length mismatch')
    size = fields['preimage_len']
    if stage == 'pinning':
        if slots or any(k in fields for k in ('t', 'n_slots', 'slot_len')):
            raise ValueError('A pinning problem has no slots')
        seq, lt = fields.get('seq_off'), fields.get('lt_off')
        if seq is None or lt is None or not seq + 4 <= lt or lt + 8 != size:
            raise ValueError('Invalid nSequence / nLockTime offsets')
    else:
        n, t = ROUNDS[stage]
        length = fields.get('slot_len')
        if 'seq_off' in fields or 'lt_off' in fields:
            raise ValueError('A round problem has no nonce offsets')
        if fields.get('t') != t or fields.get('n_slots') != n or len(slots) != n or not length:
            raise ValueError('Problem does not have the stage table')
        if any(b < a + length + 12 for a, b in zip(slots, slots[1:])) or slots[-1] + length > size:
            raise ValueError('Invalid slot offsets')
    return fields


def validate_request(data, commit):
    allowed = {'protocol', 'stage', 'attempt', 'searchVersion', 'problemBase64', 'problemSha256',
               'manifestHash', 'kernelCommit'}
    if not isinstance(data, dict) or set(data) != allowed:
        raise ValueError('Unknown, missing or potentially private fields are forbidden')
    if data['protocol'] != PROTOCOL or data['kernelCommit'] != commit:
        raise ValueError('Protocol or kernel mismatch')
    if data['searchVersion'] != VERSION:
        raise ValueError('Search scheduler version mismatch')
    stage = data['stage']
    if stage not in SHAPES or not isinstance(data['manifestHash'], str) \
            or not re.fullmatch('[a-f0-9]{64}', data['manifestHash']):
        raise ValueError('Invalid stage or manifest')
    if not isinstance(data['problemBase64'], str):
        raise ValueError('Invalid problem')
    raw = base64.b64decode(data['problemBase64'], validate=True)
    if not 64 <= len(raw) <= MAX_PROBLEM or hashlib.sha256(raw).hexdigest() != data['problemSha256']:
        raise ValueError('Problem integrity check failed')
    parse_problem(raw, stage)
    return raw, work_range(stage, data['attempt'])


def range_arguments(stage, unit):
    if stage == 'pinning':
        return ['--pin-seq', str(unit['sequence']), '--pin-seq-count', str(unit['sequenceCount']),
                '--pin-lt-start', str(unit['locktime']), '--pin-lt-count', str(unit['locktimeCount'])]
    return ['--prefix-start', unit['prefixStart'], '--prefix-count', str(unit['prefixCount'])]


def range_report(log, stage, unit):
    """The grinder's own completion line, accepted only if it describes exactly this unit."""
    lines = [ln for ln in log.splitlines() if ln.startswith('@range ')]
    if len(lines) != 1:
        return None
    try:
        report = json.loads(lines[0][len('@range '):])
    except ValueError:
        return None
    if report.get('complete') is not True or report.get('der_filter') != 1:
        return None
    if report.get('zblocks') != unit['count'] or report.get('expected') != unit['count']:
        return None
    if stage == 'pinning':
        want = {'kind': 'pin', 'seq': unit['sequence'], 'seq_count': unit['sequenceCount'],
                'lt_start': unit['locktime'], 'lt_count': unit['locktimeCount']}
    else:
        want = {'kind': 'round', 'prefix_start': int(unit['prefixStart']),
                'prefix_count': unit['prefixCount'], 'subset_start': int(unit['start'])}
    if any(report.get(k) != v for k, v in want.items()):
        return None
    if type(report.get('hits')) is not int or type(report.get('gate_hits')) is not int:
        return None
    return report


def handler(event, root=ROOT, timeout=TIMEOUT_SECONDS):
    binding = release_binding(root)
    data = event['input']
    raw, unit = validate_request(data, binding['solverCommit'])
    stage = data['stage']
    shape = SHAPES[stage]
    with tempfile.TemporaryDirectory(prefix='qsb-pqb-') as directory:
        work = pathlib.Path(directory)
        (work / 'P.txt').write_bytes(raw)
        command = [str(root / 'grind'), '--problem', 'P.json', '--hits', 'hits.txt',
                   '--der-filter', '1'] + range_arguments(stage, unit)
        start = time.monotonic()
        with open(work / 'compute.log', 'w') as output:
            process = subprocess.Popen(command, cwd=work, stdout=output, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                process.wait(timeout=timeout)
                status = 'completed' if process.returncode == 0 else 'failed'
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                status = 'interrupted'
        elapsed = time.monotonic() - start
        report = None
        candidates = []
        if status == 'completed':
            # Only the last megabyte of the log can hold the completion line.
            with open(work / 'compute.log', 'rb') as f:
                f.seek(max(0, (work / 'compute.log').stat().st_size - (1 << 20)))
                report = range_report(f.read().decode('ascii', 'replace'), stage, unit)
            hits = work / 'hits.txt'
            if report is None or not hits.is_file() or hits.stat().st_size > 64 * MAX_CANDIDATES:
                status = 'failed'           # never credit a range that did not account for itself
            else:
                candidates = sorted(ln for ln in hits.read_text().split('\n') if ln)
                pattern = '[0-9]{1,10} [0-9]{1,10}( [0-9]{1,3}){4}' if stage == 'pinning' \
                    else '[0-9]{1,3}(,[0-9]{1,3})*( [0-9]{1,3}){4}'
                if (len(candidates) != report['hits'] or len(candidates) > MAX_CANDIDATES
                        or not all(re.fullmatch(pattern, c) for c in candidates)):
                    status, candidates = 'failed', []
    result = {'status': status, 'stage': stage, 'manifestHash': data['manifestHash'],
              'attempt': data['attempt'], 'elapsedSeconds': elapsed, 'candidates': candidates,
              'verified': False, 'kernelCommit': binding['solverCommit'], 'searchVersion': VERSION,
              'workRange': unit,
              'checkpoint': 'range-complete' if status == 'completed' else 'requires-verification-or-resume'}
    if status == 'completed':
        # Trials at the 24-bit gate: the consumer can compare gateHits with trials / 2^24.
        result['trials'] = unit['count'] * shape['K'] * shape['npts'] * shape['nenc'] * shape['H']
        result['gateHits'] = report['gate_hits']
    return result
