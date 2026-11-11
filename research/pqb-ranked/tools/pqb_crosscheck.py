"""Check ranked hits against pqb's own verifier (development only; needs a pqb checkout).

    PQB_ROOT=/path/to/pqb python3 research/pqb-ranked/tools/pqb_crosscheck.py

For each fixture stage it runs the CPU-emulated adapted grinder on a few ranked ranges and gives
every hit line to pqb's `gpu.HitChecker`, which re-derives the digest from the work packet and
re-checks a sample through `grind.evaluate`. It also checks that pqb's nonce for every hit lies
inside the range the contract module states. pqb is the reference here, not this repository.
"""
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PQB = os.environ.get('PQB_ROOT')
if not PQB:
    sys.exit('set PQB_ROOT to a fireblocks-labs/pqb checkout')
sys.path.insert(0, os.path.join(PQB, 'pqb', 'src'))
sys.path.insert(0, str(ROOT / 'tests'))
sys.path.insert(0, str(ROOT / 'worker/pqb'))
import pqb_emulation as emu  # noqa: E402
import pqb_ranges as ranges  # noqa: E402
from pqb import gpu, grind  # noqa: E402

GATE_BITS = 12
CASES = {'pin': [('pin', 0x80000000, 2, 500000000, 2500), ('pin', 0xFFFFFFFD, 1, 1699997000, 3000)],
         'round0': [('round0', 0, 12), ('round0', 20000000000, 40), ('round0', ranges.prefix_total('round0') - 500, 500)],
         'round1': [('round1', 0, 25), ('round1', 150000000000, 60), ('round1', ranges.prefix_total('round1') - 800, 800)]}


def main():
    binary = emu.build()
    if not binary:
        sys.exit('no C++ compiler')
    total = 0
    for name, cases in CASES.items():
        packet = grind.Packet(json.loads((emu.FIXTURES / (name + '.packet.json')).read_text()))
        prob = gpu.problem_from_packet(packet, gate_bits=GATE_BITS)
        if gpu.problem_txt(prob).encode() != emu.problem(name):
            sys.exit('%s: the committed problem is not what pqb derives from the committed packet' % name)
        gpu.check_problem(packet, prob, samples=8)
        checker = gpu.HitChecker(packet, prob, gate_bits=GATE_BITS, canonical_first=40, canonical_every=50)
        for case in cases:
            if name == 'pin':
                _n, seq, seq_count, lt, lt_count = case
                args = ['--pin-seq', seq, '--pin-seq-count', seq_count, '--pin-lt-start', lt, '--pin-lt-count', lt_count]
                lo = (seq - ranges.SEQ_MIN) * ranges.LT_SPAN
                hi = (seq + seq_count - ranges.SEQ_MIN) * ranges.LT_SPAN
            else:
                _n, start, count = case
                args = ['--prefix-start', start, '--prefix-count', count]
                lo = ranges.subset_rank_of_prefix(name, start)
                hi = ranges.subset_rank_of_prefix(name, start + count)
            code, log, hits = emu.run(binary, emu.problem(name), args)
            if code:
                sys.exit(log)
            for line in hits:
                cand = checker.check(line)          # raises if pqb does not reproduce the hit
                if not lo <= cand.nonce < hi:
                    sys.exit('%s: hit nonce %d outside [%d, %d)' % (name, cand.nonce, lo, hi))
            total += len(hits)
            print(name, case[1:], '%d hits reproduced by pqb' % len(hits))
        print(name, checker.stats())
    print('all %d hits reproduced by pqb' % total)


if __name__ == '__main__':
    main()
