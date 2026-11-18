"""Matched ranked subrange timings in the candidate runtime on one A10G.

Run after full-unit qualification. The baseline executable must be extracted from
the previous enrolled OCI image. These smaller ranges exercise common inputs.
"""
import json
from math import comb
from pathlib import Path
import sys
import time

import run_measure as measure
from run_full_unit import verify_candidate, write_json


BASELINE_SHA = '0e811c59de2d36f66142a6f65393c55a64e0e37c7eb40df4251f86b713ef3d82'


def workload(stage, pair):
    if stage == 'pin':
        count = 160_000_000
        unit = dict(sequence=0x80000000, sequenceCount=1, locktime=500000000 + count * pair,
                    locktimeCount=count, start=count * pair, count=count)
        args = ['--pin-seq', unit['sequence'], '--pin-lt-start', unit['locktime'], '--pin-lt-count', count]
    else:
        n, t = measure.ROUNDS[stage]
        start = comb(n - 1, t - 1) * (2 * pair + 1) // 6
        args = ['--prefix-start', start, '--prefix-count', 8_000_000]
        unit = dict(start=measure._subset_rank_of_prefix(n, t, start), count=measure.expected_zblocks(stage, args))
    return args + ['--der-filter', 1], unit


def compare(gate, baseline, result, deadline):
    import reference  # mounted independent public CPU implementation
    installed = Path('/opt/qsb-pqb')
    candidate = installed / 'grind'
    binding = json.loads((gate / 'binding.json').read_text())
    if measure.sha256(baseline) != BASELINE_SHA or measure.sha256(candidate) != binding['files']['grind']:
        raise ValueError('Unexpected matched binary identity')
    result.mkdir()
    for stage in ('pin', 'round0', 'round1'):
        path = gate / 'fixtures' / (stage + '.txt')
        raw = measure.with_gate(path.read_bytes(), 24)
        prob = reference.load(path)
        for pair in range(3):
            args, unit = workload(stage, pair)
            answers = []
            order = [('baseline', baseline), ('candidate', candidate)]
            if pair % 2:
                order.reverse()
            for label, binary in order:
                measure.DEADLINE = deadline - time.time() - 90
                measure.START = time.monotonic()
                if measure.DEADLINE < 65:
                    raise TimeoutError('Insufficient time to measure and collect the next sample')
                dest = result / f'{stage}-{pair}-{label}'
                dest.mkdir()
                (dest / 'P.txt').write_bytes(raw)
                write_json(dest / 'invocation.json', dict(binarySha256=measure.sha256(binary), args=args))
                measure.FAILURE_DIR = dest / 'failures'
                measure.LAST = None
                try:
                    events, hits, wall = measure.run(binary, raw, args, timeout=60)
                finally:
                    if measure.LAST is not None:
                        for name, data in zip(('stdout.txt', 'stderr.txt', 'hits.txt'), measure.LAST[-3:]):
                            (dest / name).write_text(data)
                check_start = time.monotonic()
                report = events['range']
                z = unit['count']
                if (not report['complete'] or report['zblocks'] != z or report['expected'] != z
                        or events['done']['zblocks'] != z or sum(b['z'] for b in events['batch']) != z
                        or report['hits'] != len(hits) or len(set(hits)) != len(hits)
                        or any(report[k] != v for k, v in measure.report_identity(args).items())
                        or not measure.gate_consistent(report['gate_hits'], z, stage)
                        or 'A10G' not in events['setup']['device']):
                    raise ValueError('Matched sample failed range, output or device checks')
                for hit in hits:
                    verify_candidate(reference, prob, 'pinning' if stage == 'pin' else stage, unit, hit)
                answers.append((report['gate_hits'], hits))
                write_json(dest / 'sample.json', dict(stage=stage, pair=pair, label=label, zblocks=z,
                           processSeconds=wall, verificationSeconds=time.monotonic()-check_start,
                           steady=measure.steady(events), gateHits=report['gate_hits'], candidates=len(hits)))
            if answers[0] != answers[1]:
                raise ValueError('Baseline and candidate produced different gate counts or hits')
    write_json(result / 'completion.json', dict(status='passed', pairsPerStage=3))


if __name__ == '__main__':
    gate, baseline, result = map(Path, sys.argv[1:4])
    sys.path.insert(0, str(gate))
    compare(gate, baseline, result, int(sys.argv[4]))
