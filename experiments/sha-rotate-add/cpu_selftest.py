"""CPU-only control for verify_trace.py: no GPU, no solver binary, not native evidence.

Builds trace lines from the hash-verified public CPU reference itself, then checks that the
verifier accepts them and rejects a corrupted hash, a missing record and two hashes
swapped between recovery ids.
Usage: cpu_selftest.py CPU_REFERENCE_ROOT OUTPUT [MAX_CANDIDATES_PER_CASE]
"""
import hashlib, json, sys, tempfile
from pathlib import Path
import verify_trace
from run_trace import FIXTURES, unrank

HERE = Path(__file__).resolve().parent


def main():
    reference, output = Path(sys.argv[1]), Path(sys.argv[2])
    limit = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    if output.exists(): raise ValueError('output already exists')
    plan_raw = (HERE.parents[1] / 'worker/promotion/validation/trace-fixtures.json').read_bytes()
    if hashlib.sha256(plan_raw).hexdigest() != FIXTURES: raise ValueError('plan mismatch')
    data = verify_trace.load_public(reference, HERE / 'fixtures')
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        for name, raw in data.items():
            if name.startswith('reference/'): (root / Path(name).name).write_bytes(raw)
        sys.path.insert(0, str(root))
        from gpu_emulator import emulate_digest_round
        from bitcoin_tx import Transaction, TxIn, TxOut, find_and_delete
        tools = (emulate_digest_round, Transaction, TxIn, TxOut, find_and_delete)
        rows = []; rejected = {'corruptHash': 0, 'missingRecord': 0, 'swappedRecid': 0}; swappable = 0
        for plan in json.loads(plan_raw)['cases']:
            plan = dict(plan, count=min(plan['count'], limit))
            prefix = 'fixtures/' + plan['case'] + '/'
            state = json.loads(data[prefix + 'qsb_state.json'])
            params = json.loads(data[prefix + f"gpu_digest_r{plan['stage']}_params.json"])
            lines = []
            for rank in range(plan['start'], plan['start'] + plan['count']):
                gpu = unrank(rank)
                emulated = emulate_digest_round(params, sorted(149 - i for i in gpu), sequence=plan['sequence'], locktime=plan['locktime'])
                for bit, candidate in enumerate(emulated['candidates']):
                    lines.append('TRACE_SUB indices=' + ','.join(map(str, gpu)) + f" recid={bit} hash={candidate['puzzle_hash'].hex()}")
            def sample(log):
                return dict(count=plan['count'], rank=plan['start'], seconds=1, exit=0, timedOut=False, hitFiles={},
                            log=log + '\n[GPU 0] Done enum:\n',
                            summary=f"STATUS=EXHAUSTED 1 total_attempts={plan['count']} elapsed_s=0 hits=0")
            good = '\n'.join(lines)
            rows.append(verify_trace.check_case(plan, dict(trace=sample(good), exact=sample('')), state, params, *tools))
            flipped = lines[0][:-1] + ('0' if lines[0][-1] != '0' else '1')
            first, second = lines[0].rsplit('hash=', 1), lines[1].rsplit('hash=', 1)
            swapped = [first[0] + 'hash=' + second[1], second[0] + 'hash=' + first[1], *lines[2:]]
            distinct = first[1] != second[1]; swappable += distinct
            trials = [('corruptHash', '\n'.join([flipped, *lines[1:]])), ('missingRecord', '\n'.join(lines[1:]))]
            if distinct: trials.append(('swappedRecid', '\n'.join(swapped)))
            for key, log in trials:
                try: verify_trace.check_case(plan, dict(trace=sample(log), exact=sample('')), state, params, *tools)
                except ValueError: rejected[key] += 1
    cases = len(rows)
    result = dict(control='CPU-generated, not GPU evidence', positive=True, cases=cases, candidatesPerCaseLimit=limit,
                  candidates=sum(r['candidates'] for r in rows), hashes=sum(r['hashes'] for r in rows),
                  corruptHashRejected=rejected['corruptHash'] == cases, missingRecordRejected=rejected['missingRecord'] == cases,
                  swappedRecidRejected=swappable > 0 and rejected['swappedRecid'] == swappable, swappedRecidCases=swappable,
                  referenceFilesChecked=len(data), traceFixturesSha256=FIXTURES)
    if not (result['corruptHashRejected'] and result['missingRecordRejected'] and result['swappedRecidRejected']): raise SystemExit('verifier accepted a bad trace')
    with output.open('x') as stream: json.dump(result, stream, indent=2, sort_keys=True); stream.write('\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
