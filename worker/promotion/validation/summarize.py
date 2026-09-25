"""Validate a complete benchmark receipt before reporting measured speedups."""
import json
import statistics
import sys
from benchmark import BASELINE_SHA, CANDIDATE_SHA, hit_fields


def summarize(result, fixtures):
    if result['candidateSha256'] != CANDIDATE_SHA or result['baselineSha256'] != BASELINE_SHA:
        raise ValueError('unrecognized binaries')
    if len(result['replay']) != len(fixtures['replay']):
        raise ValueError('missing replays')
    for row, fixture in zip(result['replay'], fixtures['replay']):
        if (row['name'], row['count'], row['rank']) != (fixture['name'], 1, fixture['rank']):
            raise ValueError('replay binding mismatch')
        if hit_fields(row['hit']) != hit_fields(fixture['expected']):
            raise ValueError('replay result mismatch')
    expected = {(f['name'], i, binary) for f in fixtures['benchmark']
                for i in range(3) for binary in ('baseline', 'candidate')}
    seen = set()
    groups = {}
    for row in result['samples']:
        key = (row['name'], row['sample'], row['binary'])
        if key not in expected or key in seen:
            raise ValueError('unexpected or duplicate sample')
        seen.add(key)
        seconds = row['seconds']
        if not isinstance(seconds, (int, float)) or not 0 < seconds < 120:
            raise ValueError('invalid measurement')
        if row['count'] != 1 << 31 or row['rank'] != 0:
            raise ValueError('range mismatch')
        if row['hit']:
            raise ValueError('benchmark found new hit; independent verification required')
        groups.setdefault(row['name'], {}).setdefault(row['binary'], []).append(seconds)
    if seen != expected:
        raise ValueError('incomplete benchmark')
    output = {}
    for name, samples in groups.items():
        base, candidate = (statistics.median(samples[b]) for b in ('baseline', 'candidate'))
        output[name] = dict(baselineSeconds=samples['baseline'], candidateSeconds=samples['candidate'],
                            medianBaselineSeconds=base, medianCandidateSeconds=candidate,
                            throughputGainPercent=100*(base/candidate-1),
                            wallTimeReductionPercent=100*(1-candidate/base))
    return output


if __name__ == '__main__':
    from pathlib import Path
    print(json.dumps(summarize(json.loads(Path(sys.argv[1]).read_text()),
                              json.loads(Path(__file__).with_name('fixtures.json').read_text())), indent=2))
