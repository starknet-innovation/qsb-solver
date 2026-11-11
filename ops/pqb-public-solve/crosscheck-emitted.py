"""Recheck every retained emitted hit, including CPU-negative hits, with pinned upstream."""
import argparse
import base64
import hashlib
import json
import math
import platform
from pathlib import Path
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('upstream', type=Path)
    parser.add_argument('campaign', type=Path)
    parser.add_argument('state_directory', type=Path)
    parser.add_argument('stage', choices=('pinning', 'round1', 'round2'))
    parser.add_argument('packet_export', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--wasm-shim', action='store_true', help='Explicit supplemental pure-Python curve backend')
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    commit = subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip()
    if commit != 'eccdd09772edf14ab37fc63992b0626ad7ff2221' or subprocess.check_output(
        ['git', '-C', str(upstream), 'status', '--porcelain'], text=True).strip():
        raise ValueError('Clean pinned upstream required')
    sys.path.insert(0, str(upstream / 'pqb/src'))
    if args.wasm_shim:
        sys.path.insert(0, str(upstream / 'pqb/src/pqb/wasm/shim'))
    from pqb import gpu, grind
    import coincurve
    backend = {'implementation': 'upstream-wasm-shim' if args.wasm_shim else 'native-coincurve',
        'version': coincurve.__version__, 'python': sys.version, 'machine': platform.machine()}
    if not args.wasm_shim:
        import coincurve._libsecp256k1 as native
        if coincurve.__version__ != '21.0.0':
            raise ValueError('Install upstream pinned coincurve==21.0.0')
        backend['sharedObjectSha256'] = hashlib.sha256(Path(native.__file__).read_bytes()).hexdigest()
    exported = json.loads(args.packet_export.read_bytes())
    if 'records' in exported:
        exported = next(record for record in exported['records'] if record['stage'] == args.stage)
    raw = exported['packet']
    raw['menu']['r_inv'] = int(raw['menu']['r_inv'])
    if raw.get('pin_nonce') is not None:
        raw['pin_nonce'] = int(raw['pin_nonce'])
    raw['nonce_space'] = grind.PIN_NONCE_SPACE if raw['kind'] == 'pinning' else math.comb(len(raw['live_slots']), raw['t'])
    packet = grind.Packet(raw)
    problem = gpu.problem_from_packet(packet, gate_bits=24)
    problem_bytes = exported['problem'].encode()
    if gpu.problem_txt(problem).encode() != problem_bytes:
        raise ValueError('Upstream/consumer problem bytes differ')
    gpu.check_problem(packet, problem, samples=8, seed=1)
    records = []
    other_problems = []
    for path in sorted((args.state_directory / 'jobs').glob('*.json')):
        if not re.fullmatch(r'[a-f0-9-]{36}\.json', path.name):
            continue
        job = json.loads(path.read_bytes())
        if job['slot']['stage'] != args.stage or job['result']['status'] != 'COMPLETED':
            continue
        identity = job['slot']['identity']
        wire = (args.campaign / 's3' / identity['inputKey']).read_bytes()
        if hashlib.sha256(wire).hexdigest() != identity['inputSha256']:
            raise ValueError('Original wire input differs')
        original_problem = base64.b64decode(json.loads(wire)['input']['problemBase64'])
        if original_problem != problem_bytes:
            other_problems.append({'jobId': path.stem, 'problemSha256': hashlib.sha256(original_problem).hexdigest()})
            continue
        checker = gpu.HitChecker(packet, problem, gate_bits=24, canonical_first=40)
        candidates = []
        full = []
        for line in job['result']['output']['candidates']:
            previous = checker.full
            candidate = checker.check(line)
            candidates.append({'line': line, 'details': candidate.as_dict()})
            if checker.full > previous:
                full.append(line)
        cpu = json.loads(path.with_name(path.stem + '-cpu.json').read_bytes())['checked']
        if bool(full) != cpu['valid'] or (full and full[0] != cpu['candidate']):
            raise ValueError('Independent upstream/consumer full-solution decision differs')
        records.append({'jobId': path.stem, 'attempt': job['slot']['attempt'], 'candidates': candidates,
            'checks': checker.stats(), 'consumerDecisionMatched': True})
    if not records:
        raise ValueError('No completed units checked')
    result = {'format': 'qsb-upstream-emitted-check-v1', 'upstreamCommit': commit, 'stage': args.stage,
        'validatorSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'packetExportSha256': hashlib.sha256(args.packet_export.read_bytes()).hexdigest(),
        'problemSha256': hashlib.sha256(problem_bytes).hexdigest(), 'gateBits': 24, 'curveBackend': backend,
        'sighashSamples': 8, 'completedUnits': len(records), 'otherProblemJobsNotChecked': other_problems,
        'records': records}
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}))


if __name__ == '__main__':
    main()
