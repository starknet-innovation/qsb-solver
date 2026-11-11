"""Native correctness and matched timing of the ranked PQB grinder, in one bounded run.

    python3 run_measure.py BUNDLE RESULT.json

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
                           and rep.get('exact_zblocks') == case['exactZblocks'])
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
        ok = ok and rep.get('complete') is True and rep.get('zblocks') == rep.get('expected')
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
    bundle, result = Path(sys.argv[1]), Path(sys.argv[2])
    if result.exists():
        sys.exit('result exists: this run is one-shot')
    result.write_text(json.dumps({'status': 'started'}) + '\n')          # the one-shot marker
    global FAILURE_DIR
    FAILURE_DIR = result.parent / 'failed-invocations'
    expected = json.loads((bundle / 'expected.json').read_text())
    out = {'format': 'qsb-pqb-measure-result-v1', 'status': 'incomplete',
           'binaries': {n: sha256(bundle / n) for n in ('grind-ranked', 'grind-upstream')},
           'expectedSha256': sha256(bundle / 'expected.json'),
           'settings': {'samples': SAMPLES, 'seconds': SECONDS, 'strata': STRATA, 'skipBatches': SKIP_BATCHES,
                        'requireSteady': REQUIRE_STEADY}}
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
        out['correctnessPassed'] = all(c['pass'] for c in out['correctness'])
        # Timing a binary that computes wrong answers would measure nothing useful.
        out['timing'] = timing(bundle) if out['correctnessPassed'] else None
        timed = out['timing'] and all('summary' in v and all(s.get('gateConsistent') and s.get('complete', True)
                                                            for s in v['samples']) for v in out['timing'].values())
        # every upstream and ranked sample must have reached steady state, or there is no comparison
        unsteady = sorted(stage for stage, v in (out['timing'] or {}).items()
                          if len(v['samples']) != 2 * SAMPLES or any(not s.get('steady') for s in v['samples']))
        if out['timing'] is not None:
            out['stagesWithoutSteadyState'] = unsteady
        out['status'] = 'passed' if out['correctnessPassed'] and timed and not (REQUIRE_STEADY and unsteady) else 'failed'
    except Exception as e:                               # noqa: BLE001  a one-shot run must still report
        out.setdefault('correctnessPassed', False)
        out.update(status='failed', error='%s: %s' % (type(e).__name__, str(e)[:400]))
    out['elapsedSeconds'] = time.monotonic() - START
    result.write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps({'status': out['status'], 'correctnessPassed': out['correctnessPassed']}))
    sys.exit(0 if out['status'] == 'passed' else 1)


if __name__ == '__main__':
    main()
