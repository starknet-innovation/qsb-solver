"""The adapted PQB grinder, built as plain C++, against an independent slow enumeration.

Each case compares the complete hit set of a ranked range, so a skipped trial and an invented
hit both fail. This is CPU emulation of the kernel source: it is not native GPU evidence.
"""
import hashlib
import json
import random
import sys
import tempfile
import unittest
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
sys.path.insert(0, str(ROOT / 'research/pqb-ranked/tests'))
import pqb_emulation as emu  # noqa: E402
import reference  # noqa: E402

BINARY = emu.build()
SMALL_BATCHES = {'QG_NZ_MAX': '256'}        # several batches, two in flight, for a small range


def report(log):
    lines = [ln for ln in log.splitlines() if ln.startswith('@range ')]
    return json.loads(lines[0][len('@range '):]) if len(lines) == 1 else None


def der_shape(d):
    """The necessary shape of a 32-byte StrictDER signature plus hashtype, from its definition."""
    lr = d[3]
    return 1 <= lr <= 24 and d[4 + lr] == 2 and d[5 + lr] == 25 - lr


@unittest.skipUnless(BINARY, 'no C++ compiler')
class RankedEmulationTest(unittest.TestCase):
    def pin(self, seq, seq_count, lt_start, lt_count, env=None):
        raw = emu.problem('pin')
        code, log, hits = emu.run(BINARY, raw, ['--pin-seq', seq, '--pin-seq-count', seq_count,
                                               '--pin-lt-start', lt_start, '--pin-lt-count', lt_count], env)
        self.assertEqual(code, 0, log)
        rep = report(log)
        self.assertTrue(rep and rep['complete'], log)
        self.assertEqual(rep['zblocks'], seq_count * lt_count)
        prob = reference.load(emu.FIXTURES / 'pin.txt')
        want = reference.pin_hits(prob, seq, seq_count, lt_start, lt_count)
        self.assertEqual(hits, want)
        self.assertEqual(rep['hits'], len(want))
        return want

    def rounds(self, name, start, count, env=None):
        raw = emu.problem(name)
        code, log, hits = emu.run(BINARY, raw, ['--prefix-start', start, '--prefix-count', count], env)
        self.assertEqual(code, 0, log)
        rep = report(log)
        self.assertTrue(rep and rep['complete'], log)
        prob = reference.load(emu.FIXTURES / (name + '.txt'))
        subsets = reference.round_subsets_at(prob, start, count)
        self.assertEqual(rep['zblocks'], len(subsets))
        # the range is the contiguous run of pqb subset ranks the grinder says it is
        n = prob['n_slots']
        self.assertEqual(rep['subset_start'], reference.subset_rank(subsets[0], n))
        self.assertEqual([reference.subset_rank(s, n) for s in subsets],
                         list(range(rep['subset_start'], rep['subset_start'] + len(subsets))))
        want = reference.round_hits(prob, subsets)
        self.assertEqual(hits, want)
        return want

    def test_pin_ranges(self):
        found = self.pin(0x80000003, 2, 500000000, 300)
        found += self.pin(0xFFFFFFFD, 1, 1699999800, 200)           # the last usable nonces
        found += self.pin(0x80000000, 3, 1234567890, 700, SMALL_BATCHES)
        self.assertGreater(len(found), 10)                           # the comparison is not vacuous

    def test_round0_ranges(self):
        total = comb(108, 7)
        found = self.rounds('round0', 0, 3)                          # most completions per prefix
        found += self.rounds('round0', total - 60, 60)               # the last prefixes, one completion
        found += self.rounds('round0', 12345678901, 9, SMALL_BATCHES)
        self.assertGreater(len(found), 20)

    def test_round1_ranges(self):
        total = comb(100, 8)
        found = self.rounds('round1', 0, 8)
        found += self.rounds('round1', total - 60, 60)
        found += self.rounds('round1', 98765432101, 12, SMALL_BATCHES)
        self.assertGreater(len(found), 10)

    def test_ranges_outside_the_space_are_refused(self):
        pin, r0 = emu.problem('pin'), emu.problem('round0')
        bad = [(pin, ['--pin-seq', 0x7FFFFFFF]),
               (pin, ['--pin-seq', 0xFFFFFFFD, '--pin-seq-count', 2]),
               (pin, ['--pin-seq', 0x80000000, '--pin-lt-start', 499999999]),
               (pin, ['--pin-seq', 0x80000000, '--pin-lt-start', 1699999999, '--pin-lt-count', 2]),
               (pin, ['--prefix-start', 0, '--prefix-count', 1]),
               (r0, ['--pin-seq', 0x80000000]),
               (r0, ['--prefix-start', comb(108, 7), '--prefix-count', 1]),
               (r0, ['--prefix-start', comb(108, 7) - 1, '--prefix-count', 2]),
               (r0, ['--prefix-start', 0, '--prefix-count', 0]),
               (r0, ['--prefix-start', 0, '--prefix-count', 1, '--unknown', 1]),
               (r0, ['--der-filter', 1])]
        for raw, args in bad:
            with self.subTest(args=args):
                code, log, _hits = emu.run(BINARY, raw, args)
                self.assertNotEqual(code, 0, log)
                self.assertIsNone(report(log))

    def test_der_shape_predicate(self):
        rng = random.Random(20261111)
        digests = []
        for lr in range(0, 27):                                      # every length, valid and not
            for _ in range(8):
                d = bytearray(rng.randbytes(32))
                d[0:4] = bytes([0x30, 0x1D, 0x02, lr])
                if lr + 5 < 32:
                    d[4 + lr], d[5 + lr] = 2, (25 - lr) & 0xFF
                digests.append(bytes(d))
                for at in (4 + lr, 5 + lr):                          # one wrong structural byte
                    if at < 32:
                        e = bytearray(d)
                        e[at] ^= 1 << rng.randrange(8)
                        digests.append(bytes(e))
        digests += [rng.randbytes(32) for _ in range(2000)]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'digests.txt'
            path.write_text(''.join(d.hex() + '\n' for d in digests))
            code, log, _ = emu.run(BINARY, emu.problem('pin'), ['--der-shape-file', path])
        self.assertEqual(code, 0, log)
        self.assertEqual(log.split(), ['1' if der_shape(d) else '0' for d in digests])
        self.assertGreater(sum(map(der_shape, digests)), 150)

    def test_der_filter_counts_gate_hits_and_reports_only_shaped_ones(self):
        prob = reference.load(emu.FIXTURES / 'pin.txt')
        prob['gate_bits'] = 1                                        # half of all digests pass
        raw = emu.problem('pin', gate_bits=1)
        # exact gate count on a small range
        args = ['--pin-seq', 0x80000005, '--pin-lt-start', 600000000, '--pin-lt-count', 64]
        code, log, hits = emu.run(BINARY, raw, args + ['--der-filter', 1])
        self.assertEqual(code, 0, log)
        rep = report(log)
        gate = reference.pin_hits(prob, 0x80000005, 1, 600000000, 64)
        self.assertEqual((rep['der_filter'], rep['gate_hits']), (1, len(gate)))
        shaped = [ln for ln in gate if der_shape(reference.pin_digest(prob, ln))]
        self.assertEqual(hits, shaped)
        # a larger range, where shaped hits are expected: each one re-derives and has the shape,
        # and the filter is the only difference from the gate
        n = 60000
        args = ['--pin-seq', 0x80000006, '--pin-lt-start', 700000000, '--pin-lt-count', n]
        code, log, hits = emu.run(BINARY, raw, args + ['--der-filter', 1])
        self.assertEqual(code, 0, log)
        rep = report(log)
        trials = n * 72
        self.assertLess(abs(rep['gate_hits'] - trials / 2), 6 * (trials / 4) ** 0.5)
        self.assertEqual(rep['hits'], len(hits))
        self.assertGreater(len(hits), 0)                             # ~3 expected (2^-20.4 a trial)
        for ln in hits:
            d = reference.pin_digest(prob, ln)
            self.assertTrue(d[0] < 0x80 and der_shape(d), ln)


if __name__ == '__main__':
    unittest.main()
