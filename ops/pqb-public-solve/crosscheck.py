"""Locally rederive real public solutions using a clean pinned upstream checkout.

Only adapt the consumer's JSON scalar representation and add nonce-space metadata.
The upstream GPU problem bytes, canonical transaction digest and full predicate must agree.
This is neither a wallet witness nor a consensus/miner test.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('upstream', type=Path)
    parser.add_argument('export', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    commit = subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip()
    if commit != 'eccdd09772edf14ab37fc63992b0626ad7ff2221' or subprocess.check_output(
        ['git', '-C', str(upstream), 'status', '--porcelain'], text=True).strip():
        raise ValueError('Clean pinned upstream checkout required')
    sys.path[:0] = [str(upstream / 'pqb/src/pqb/wasm/shim'), str(upstream / 'pqb/src')]
    from pqb import gpu, grind
    payload = args.export.read_bytes()
    exported = json.loads(payload)
    if exported['format'] != 'qsb-public-upstream-crosscheck-v1':
        raise ValueError('Unexpected export')
    stages = [r['stage'] for r in exported['records']]
    if not stages or len(stages) > 3 or len(set(stages)) != len(stages) or any(
        stage not in ('pinning', 'round1', 'round2') for stage in stages):
        raise ValueError('One to three distinct accepted stages required')
    records = []
    for record in exported['records']:
        raw = record['packet']
        raw['menu']['r_inv'] = int(raw['menu']['r_inv'])
        if raw.get('pin_nonce') is not None:
            raw['pin_nonce'] = int(raw['pin_nonce'])
        raw['nonce_space'] = grind.PIN_NONCE_SPACE if raw['kind'] == 'pinning' else math.comb(len(raw['live_slots']), raw['t'])
        packet = grind.Packet(raw)
        problem = gpu.problem_from_packet(packet, gate_bits=24)
        if gpu.problem_txt(problem) != record['problem']:
            raise ValueError('Consumer/upstream problem bytes differ: ' + record['stage'])
        gpu.check_problem(packet, problem, samples=8, seed=1)
        checker = gpu.HitChecker(packet, problem, gate_bits=24, canonical_first=40)
        candidate = checker.check(record['candidate'])
        stats = checker.stats()
        if stats['full_solutions'] != 1 or stats['canonical_rechecks'] != 1:
            raise ValueError('Upstream did not independently verify full solution')
        records.append({k: record[k] for k in ('stage', 'jobId', 'candidate')} | {
            'problemSha256': hashlib.sha256(record['problem'].encode()).hexdigest(),
            'candidateDetails': candidate.as_dict(), 'checks': stats, 'sighashSamples': 8})
    result = {'format': 'qsb-public-upstream-crosscheck-result-v1', 'upstreamCommit': commit,
        'exportSha256': hashlib.sha256(payload).hexdigest(), 'gateBits': 24,
        'hybridKeysMineable': grind.HYBRID_KEYS_MINEABLE, 'records': records,
        'scope': 'Public problem, canonical transaction digest and full predicate; no witness, consensus or miner execution'}
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
