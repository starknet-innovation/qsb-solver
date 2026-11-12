"""Native correctness and matched timing of the ranked PQB grinder, in one bounded run.

    python3 run_measure.py BUNDLE RESULT.json [--correctness-only]

BUNDLE holds grind-ranked and grind-upstream (same compiler and flags), fixtures/, expected.json.
Public synthetic inputs only. One process on one GPU, nothing else running.

Phase 1, correctness: each case in expected.json is a small ranked range whose complete hit set
was computed beforehand by the independent reference. The grinder's hits must equal it exactly.

Phase 2, timing: per stage, upstream's random search and the ranked walk alternate on the same
GPU at the production 24-bit gate. Rates are z-blocks per second in steady state (the first
batches of each process are excluded) and, separately, per whole process including start-up.
A ranked round sample is several equal-sized prefix ranges spread evenly over the prefix space,
because the work per z-block depends on where a prefix sits and upstream draws prefixes
uniformly. Within one range the prefixes are still consecutive, so this approximates a uniform
draw; it is not one.

The result records every sample. It grants no range credit and is not a full solve.
"""
import hashlib
import argparse
import json
import math
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

TRIES = {'pin': 72, 'round0': 192, 'round1': 64}
ROUNDS = {'round0': (109, 8), 'round1': (101, 9)}
LT_SPAN = 1200000000
SAMPLES = int(os.environ.get('QSB_MEASURE_SAMPLES', '3'))
SECONDS = float(os.environ.get('QSB_MEASURE_SECONDS', '10'))
STRATA = int(os.environ.get('QSB_MEASURE_STRATA', '6'))
DEADLINE = float(os.environ.get('QSB_MEASURE_DEADLINE', '600'))
SKIP_BATCHES = 3
START = time.monotonic()
FAILURE_DIR = None          # set by the caller: inputs and full output of failed invocations go here
LAST = None                 # the most recent invocation: (binary, problem, args, env, stdout, stderr, hits)
# A measurement needs a steady-state rate from every sample. Only the emulated dry run, which cannot
# reach steady state in a short sample, turns this off; the result records the setting.
REQUIRE_STEADY = os.environ.get('QSB_MEASURE_REQUIRE_STEADY', '1') != '0'
# A result must name the device that produced it, and that device must be a GPU. Only the emulated
# dry run accepts the CPU emulation build; the result records the setting.
ALLOW_EMULATION = os.environ.get('QSB_MEASURE_ALLOW_EMULATION') == '1'
MAX_KEPT_FAILURES = 20
KEEP_BYTES = 400000


class Failed(Exception):
    pass


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _text(value):
    if value is None:
        return ''
    return value if isinstance(value, str) else value.decode('ascii', 'replace')


def keep_failure(reason, binary, problem, args, env, stdout, stderr, hits):
    """A failed invocation's exact inputs and whole output, kept for the run's durable receipts."""
    if FAILURE_DIR is None:
        return
    root = Path(FAILURE_DIR)
    root.mkdir(parents=True, exist_ok=True)
    index = len(list(root.iterdir()))
    if index >= MAX_KEPT_FAILURES:
        return
    d = root / ('%02d' % index)
    d.mkdir()
    (d / 'P.txt').write_bytes(problem)
    (d / 'stdout.txt').write_text(_text(stdout)[-KEEP_BYTES:])
    (d / 'stderr.txt').write_text(_text(stderr)[-KEEP_BYTES:])
    (d / 'hits.txt').write_text(_text(hits)[-KEEP_BYTES:])
    (d / 'invocation.json').write_text(json.dumps({
        'reason': reason, 'binary': Path(binary).name, 'binarySha256': sha256(binary),
        'problemSha256': hashlib.sha256(problem).hexdigest(), 'args': [str(a) for a in args], 'env': env or {}},
        indent=1) + '\n')


def run(binary, problem, args, env=None, timeout=120):
    """One grinder process. Returns its events, hit lines and wall time."""
    left = DEADLINE - (time.monotonic() - START)
    if left < 5:
        raise Failed('out of time')
    with tempfile.TemporaryDirectory(prefix='pqb-measure-') as d:
        (Path(d) / 'P.txt').write_bytes(problem)
        hits = Path(d) / 'hits.txt'
        t0 = time.monotonic()
        try:
            done = subprocess.run([str(binary), '--problem', 'P.json', '--hits', 'hits.txt'] + [str(a) for a in args],
                                  cwd=d, capture_output=True, text=True, timeout=min(timeout, left),
                                  env=dict(os.environ, **(env or {})))
        except subprocess.TimeoutExpired as e:
            keep_failure('timeout', binary, problem, args, env, e.stdout, e.stderr,
                         hits.read_text() if hits.is_file() else '')
            raise
        wall = time.monotonic() - t0
        hits_text = hits.read_text() if hits.is_file() else ''
    global LAST
    LAST = (binary, problem, args, env, done.stdout, done.stderr, hits_text)
    lines = sorted(ln for ln in hits_text.split('\n') if ln)
    events, problem_with_output = {'batch': []}, None
    for ln in done.stdout.splitlines():
        for tag in ('setup', 'batch', 'range', 'done'):
            if ln.startswith('@%s ' % tag):
                try:
                    value = json.loads(ln[len(tag) + 2:])
                except ValueError:
                    problem_with_output = 'malformed @%s line' % tag
                    continue
                if tag == 'batch':
                    events['batch'].append(value)
                elif tag in events:
                    # one of each per process: a second completion line must not replace the first
                    problem_with_output = 'duplicate @%s line' % tag
                else:
                    events[tag] = value
    if done.returncode:
        keep_last('exit %d' % done.returncode)
        raise Failed('exit %d: %s' % (done.returncode, (done.stderr or done.stdout)[-400:]))
    if problem_with_output:
        keep_last(problem_with_output)
        raise Failed(problem_with_output)
    return events, lines, wall


def keep_last(reason):
    """Keep the most recent invocation's artifacts: used when its output is judged wrong afterwards."""
    if LAST is not None:
        keep_failure(reason, *LAST)


def steady(events):
    """(z-blocks, seconds) over the batches after start-up; None if there are too few."""
    rows = events['batch'][SKIP_BATCHES:]
    z, s = sum(b['z'] for b in rows), sum(b['wall_ms'] for b in rows) / 1e3
    return (z, s) if len(rows) >= 3 and s > 0 else None


def with_gate(raw, bits):
    if raw.count(b'gate_bits 12\n') != 1:
        raise Failed('unexpected fixture gate')
    return raw.replace(b'gate_bits 12\n', b'gate_bits %d\n' % bits)


def report_identity(args):
    """What a completion report must say about the range and filter these arguments ask for."""
    given = {str(args[i]): int(args[i + 1]) for i in range(0, len(args), 2)}
    want = {'der_filter': given.get('--der-filter', 0)}
    if '--pin-seq' in given:
        want.update(kind='pin', seq=given['--pin-seq'], seq_count=given.get('--pin-seq-count', 1),
                    lt_start=given.get('--pin-lt-start', 500000000), lt_count=given.get('--pin-lt-count', LT_SPAN))
    else:
        want.update(kind='round', prefix_start=given['--prefix-start'], prefix_count=given['--prefix-count'])
    return want


def _subset_rank_of_prefix(n, t, prefix_rank):
    """The first t-subset rank of range(n) whose (t-1)-prefix has this lexicographic rank."""
    if prefix_rank == math.comb(n - 1, t - 1):
        return math.comb(n, t)
    prefix, x, rank = [], 0, prefix_rank
    while len(prefix) < t - 1:
        c = math.comb(n - 1 - x - 1, t - 1 - len(prefix) - 1)
        if rank < c:
            prefix.append(x)
        else:
            rank -= c
        x += 1
    subset, total, prev = prefix + [prefix[-1] + 1], 0, -1
    for k, value in enumerate(subset):
        for y in range(prev + 1, value):
            total += math.comb(n - y - 1, t - k - 1)
        prev = value
    return total


def expected_zblocks(stage, args):
    """How many z-blocks a ranked range holds, computed here and not taken from the grinder."""
    given = {str(args[i]): int(args[i + 1]) for i in range(0, len(args), 2)}
    if stage == 'pin':
        return given.get('--pin-seq-count', 1) * given.get('--pin-lt-count', LT_SPAN)
    n, t = ROUNDS[stage]
    start, count = given['--prefix-start'], given['--prefix-count']
    return _subset_rank_of_prefix(n, t, start + count) - _subset_rank_of_prefix(n, t, start)


def write_atomic(path, text):
    """Replace a receipt whole: a crash must leave the old one or the new one, never a fragment."""
    temporary = Path(str(path) + '.tmp')
    with open(temporary, 'w') as stream:
        stream.write(text)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    directory = os.open(Path(path).parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def correctness(bundle, expected):
    out = []
    for case in expected['cases']:
        raw = (bundle / 'fixtures' / case['problem']).read_bytes()
        if case['problem'] != 'pin-planted.txt':
            raw = with_gate(raw, case['gateBits'])
        row = {'label': case['label'], 'zblocks': case['zblocks'], 'expectedHits': len(case['hits'])}
        try:
            events, hits, _wall = run(bundle / 'grind-ranked', raw, case['args'], case['env'])
            rep = events.get('range') or {}
            row.update(hits=len(hits), report=rep)
            row['pass'] = (hits == case['hits'] and rep.get('complete') is True
                           and rep.get('zblocks') == case['zblocks'] == rep.get('expected')
                           and rep.get('gate_hits') == case['gateHits']
                           and rep.get('exact_zblocks') == case['exactZblocks']
                           # the completion report must also be one the worker would accept: it
                           # counts the hits it wrote and names the range and filter it was given
                           and rep.get('hits') == len(hits)
                           and all(rep.get(k) == v for k, v in report_identity(case['args']).items()))
            if not row['pass']:
                keep_last('wrong result for ' + case['label'])   # exit 0, but not the expected answer
        except (Failed, subprocess.TimeoutExpired, ValueError) as e:
            row.update({'pass': False, 'error': str(e)[:400]})
        out.append(row)
    return out


def gate_consistent(hits, zblocks, stage):
    mean = zblocks * TRIES[stage] / 2.0 ** 24
    return abs(hits - mean) <= 6 * math.sqrt(mean) + 6


def upstream_sample(bundle, stage, raw):
    events, hits, wall = run(bundle / 'grind-upstream', raw, ['--seconds', SECONDS], timeout=SECONDS + 60)
    z = events['done']['zblocks']
    st = steady(events)
    return {'mode': 'upstream-random', 'zblocks': z, 'processSeconds': wall, 'gateHits': len(hits),
            'steady': st, 'gateConsistent': gate_consistent(len(hits), z, stage)}


def ranked_sample(bundle, stage, raw, z_rate, index):
    """A ranked sample sized from the z-block rate just measured for upstream."""
    parts, z, wall, gate, st_z, st_s, ok = [], 0, 0.0, 0, 0, 0.0, True
    if stage == 'pin':
        count = int(min(LT_SPAN, max(4096, z_rate * SECONDS)))
        ranges = [['--pin-seq', 0x80000000 + 1000 + index, '--pin-lt-start', 500000000, '--pin-lt-count', count]]
    else:
        n, t = ROUNDS[stage]
        total = math.comb(n - 1, t - 1)
        per = int(max(64, z_rate * SECONDS / STRATA / (n / t)))     # n / t completions per prefix on average
        per = min(per, total // (2 * STRATA * SAMPLES))            # SAMPLES slices fit in each stratum's half-width
        # strata evenly spaced over the prefix space; each sample takes a fresh slice of each
        ranges = [['--prefix-start', (2 * k + 1) * total // (2 * STRATA) + index * per, '--prefix-count', per]
                  for k in range(STRATA)]
    for args in ranges:
        events, hits, w = run(bundle / 'grind-ranked', raw, args + ['--der-filter', 1], timeout=SECONDS * 6 + 60)
        rep = events.get('range') or {}
        # The sample must be the range that was asked for: the right identity and filter, the work
        # count this script computes for that range, and a hit count matching the lines written.
        this_ok = (rep.get('complete') is True and rep.get('zblocks') == rep.get('expected') == expected_zblocks(stage, args)
                   and rep.get('hits') == len(hits)
                   and all(rep.get(k) == v for k, v in report_identity(args + ['--der-filter', 1]).items()))
        if not this_ok:
            keep_last('timing sample does not describe the requested range')
        ok = ok and this_ok
        st = steady(events)
        if st is None:
            st_z = None
        elif st_z is not None:
            st_z, st_s = st_z + st[0], st_s + st[1]
        z, wall, gate = z + rep.get('zblocks', 0), wall + w, gate + rep.get('gate_hits', 0)
        parts.append({'args': args, 'zblocks': rep.get('zblocks'), 'processSeconds': w, 'steady': st,
                      'exactZblocks': rep.get('exact_zblocks'), 'shapedHits': len(hits)})
    return {'mode': 'ranked', 'zblocks': z, 'processSeconds': wall, 'gateHits': gate,
            'steady': (st_z, st_s) if st_z is not None else None, 'complete': ok,
            'gateConsistent': gate_consistent(gate, z, stage), 'parts': parts}


def timing(bundle):
    out = {}
    for stage in ('pin', 'round0', 'round1'):
        raw = with_gate((bundle / 'fixtures' / (stage + '.txt')).read_bytes(), 24)
        samples = []
        try:
            for i in range(SAMPLES):
                up = upstream_sample(bundle, stage, raw)
                samples.append(up)
                rate = up['steady'][0] / up['steady'][1] if up['steady'] else up['zblocks'] / up['processSeconds']
                samples.append(ranked_sample(bundle, stage, raw, rate, i))
            out[stage] = {'samples': samples, 'summary': summarise(samples, stage)}
        except Exception as e:                           # noqa: BLE001  keep what was measured, whatever broke
            out[stage] = {'samples': samples, 'error': '%s: %s' % (type(e).__name__, str(e)[:400])}
    return out


def summarise(samples, stage):
    summary = {}
    for mode in ('upstream-random', 'ranked'):
        rows = [s for s in samples if s['mode'] == mode]
        st = [s['steady'][0] / s['steady'][1] for s in rows if s['steady']]
        whole = [s['zblocks'] / s['processSeconds'] for s in rows]
        summary[mode] = {'steadyZPerSecond': sorted(st), 'processZPerSecond': sorted(whole),
                         'medianSteadyTrialsPerSecond': sorted(st)[len(st) // 2] * TRIES[stage] if len(st) == len(rows) else None}
    a, b = summary['ranked']['medianSteadyTrialsPerSecond'], summary['upstream-random']['medianSteadyTrialsPerSecond']
    summary['rankedOverUpstreamSteady'] = a / b if a and b else None
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bundle', type=Path)
    parser.add_argument('result', type=Path)
    parser.add_argument('--correctness-only', action='store_true',
                        help='Run the committed correctness cases; collect no performance samples')
    args = parser.parse_args()
    bundle, result = args.bundle, args.result
    if result.exists():
        sys.exit('result exists: this run is one-shot')
    result.write_text(json.dumps({'status': 'started'}) + '\n')          # the one-shot marker
    global FAILURE_DIR
    FAILURE_DIR = result.parent / 'failed-invocations'
    expected = json.loads((bundle / 'expected.json').read_text())
    out = {'format': 'qsb-pqb-correctness-result-v1' if args.correctness_only else 'qsb-pqb-measure-result-v1',
           'mode': 'correctness-only' if args.correctness_only else 'correctness-and-timing',
           'status': 'incomplete',
           'binaries': {n: sha256(bundle / n) for n in ('grind-ranked', 'grind-upstream')},
           'expectedSha256': sha256(bundle / 'expected.json'),
           'settings': {'samples': SAMPLES, 'seconds': SECONDS, 'strata': STRATA, 'skipBatches': SKIP_BATCHES,
                        'requireSteady': REQUIRE_STEADY, 'allowEmulation': ALLOW_EMULATION}}
    for name, digest in expected['fixtures'].items():
        if sha256(bundle / 'fixtures' / name) != digest:
            sys.exit('fixture differs from expected.json: ' + name)
    try:
        events, _hits, _wall = run(bundle / 'grind-ranked', with_gate((bundle / 'fixtures/pin.txt').read_bytes(), 12),
                                   ['--pin-seq', 0x80000000, '--pin-lt-start', 500000000, '--pin-lt-count', 256])
        out['device'] = events.get('setup')
    except (Failed, subprocess.TimeoutExpired) as e:
        out['device'] = {'error': str(e)[:400]}
    try:
        out['correctness'] = correctness(bundle, expected)
        out['correctnessPassed'] = bool(out['correctness']) and all(c['pass'] for c in out['correctness'])
        # Timing a binary that computes wrong answers would measure nothing useful.
        out['timing'] = timing(bundle) if out['correctnessPassed'] and not args.correctness_only else None
        timed = out['timing'] and all('summary' in v and all(s.get('gateConsistent') and s.get('complete', True)
                                                            for s in v['samples']) for v in out['timing'].values())
        # every upstream and ranked sample must have reached steady state, or there is no comparison
        unsteady = sorted(stage for stage, v in (out['timing'] or {}).items()
                          if len(v['samples']) != 2 * SAMPLES or any(not s.get('steady') for s in v['samples']))
        if out['timing'] is not None:
            out['stagesWithoutSteadyState'] = unsteady
        # the probe's single @setup record names the device; without it the result is unattributable
        device = out['device'].get('device') if isinstance(out.get('device'), dict) else None
        named = isinstance(device, str) and bool(device)
        out['nativeDevice'] = named and device != 'cpu-emulation'
        device_ok = named and (out['nativeDevice'] or ALLOW_EMULATION)
        accepted = device_ok and (out['correctnessPassed'] if args.correctness_only else (
            out['correctnessPassed'] and timed and not (REQUIRE_STEADY and unsteady)))
        out['status'] = 'passed' if accepted else 'failed'
    except Exception as e:                               # noqa: BLE001  a one-shot run must still report
        out.setdefault('correctnessPassed', False)
        out.update(status='failed', error='%s: %s' % (type(e).__name__, str(e)[:400]))
    out['elapsedSeconds'] = time.monotonic() - START
    write_atomic(result, json.dumps(out, indent=1) + '\n')
    print(json.dumps({'status': out['status'], 'correctnessPassed': out['correctnessPassed']}))
    sys.exit(0 if out['status'] == 'passed' else 1)


if __name__ == '__main__':
    main()
