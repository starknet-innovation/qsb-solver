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

    def test_exact_host_path_equals_the_reference(self):
        # test hook: every thread is treated as exceptional, so the host computes every z-block
        force = {'QG_TEST_ALL_EXCEPTIONAL': '1'}
        cases = [('pin', ['--pin-seq', 0x80000009, '--pin-lt-start', 800000000, '--pin-lt-count', 130]),
                 ('round0', ['--prefix-start', 1, '--prefix-count', 2]),
                 ('round1', ['--prefix-start', 2, '--prefix-count', 5])]
        for name, args in cases:
            with self.subTest(stage=name):
                prob = reference.load(emu.FIXTURES / (name + '.txt'))
                if name == 'pin':
                    want = reference.pin_hits(prob, args[1], 1, args[3], args[5])
                else:
                    want = reference.round_hits(prob, reference.round_subsets_at(prob, args[1], args[3]))
                code, log, hits = emu.run(BINARY, emu.problem(name), args, force)
                self.assertEqual(code, 0, log)
                rep = report(log)
                self.assertEqual(rep['exact_zblocks'], rep['zblocks'])
                self.assertEqual(hits, want)
                self.assertGreater(len(want), 0)
                code, log, normal = emu.run(BINARY, emu.problem(name), args)
                self.assertEqual((report(log)['exact_zblocks'], normal), (0, want))
        # and with the shape filter: the host counts gate hits the way the device does
        prob = reference.load(emu.FIXTURES / 'pin.txt')
        prob['gate_bits'] = 1
        args = ['--pin-seq', 0x80000005, '--pin-lt-start', 600000000, '--pin-lt-count', 40, '--der-filter', 1]
        code, log, hits = emu.run(BINARY, emu.problem('pin', gate_bits=1), args, force)
        self.assertEqual(code, 0, log)
        gate = reference.pin_hits(prob, 0x80000005, 1, 600000000, 40)
        self.assertEqual(report(log)['gate_hits'], len(gate))
        self.assertEqual(hits, [ln for ln in gate if der_shape(reference.pin_digest(prob, ln))])

    def test_a_menu_point_equal_to_the_sighash_point_is_handled_exactly(self):
        # Plant the exceptional case: menu point C[0][0] = W and C[0][1] = -W for one z-block of
        # the range, so W + C[0][0] is a doubling and W + C[0][1] is the point at infinity. The
        # incomplete device formulas cannot compute that thread; the result must still be exact.
        seq, lt0, count, target = 0x8000000A, 900000000, 48, 900000021
        prob = reference.load(emu.FIXTURES / 'pin.txt')
        w = reference.pin_point(prob, seq, target)
        raw = emu.problem('pin', gate_bits=3)
        lines = raw.decode().split('\n')
        for i, ln in enumerate(lines):
            if ln.startswith('C 0 0 '):
                lines[i] = 'C 0 0 %064x %064x' % w
            elif ln.startswith('C 0 1 '):
                lines[i] = 'C 0 1 %064x %064x' % (w[0], reference.P - w[1])
        raw = '\n'.join(lines).encode()
        prob['C'][0, 0], prob['C'][0, 1], prob['gate_bits'] = w, (w[0], reference.P - w[1]), 3
        want = reference.pin_hits(prob, seq, 1, lt0, count)
        code, log, hits = emu.run(BINARY, raw, ['--pin-seq', seq, '--pin-lt-start', lt0, '--pin-lt-count', count])
        self.assertEqual(code, 0, log)
        rep = report(log)
        self.assertTrue(rep['complete'])
        self.assertEqual(rep['exact_zblocks'], 4)                    # the one thread that holds it
        self.assertEqual(hits, want)
        # the doubled point really is among the trials compared, and infinity yields no key
        doubled = [ln for ln in reference.pin_hits(dict(prob, gate_bits=0), seq, 1, target, 1)]
        self.assertEqual(sum(ln.split()[2:4] == ['0', '0'] for ln in doubled), 3)
        self.assertEqual(sum(ln.split()[2:4] == ['0', '1'] for ln in doubled), 0)

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
               (r0, ['--der-filter', 1]),
               # counts that would wrap a 64-bit sum past the bounds check
               (pin, ['--pin-seq', 0x80000000, '--pin-seq-count', 18446744073709551615]),
               (pin, ['--pin-seq', 0x80000000, '--pin-lt-count', 18446744073709551615]),
               (pin, ['--pin-seq', 0x80000000, '--pin-seq-count', 0x7FFFFFFF]),
               # malformed numbers, and range options without the option that turns ranked mode on
               (pin, ['--pin-seq', 'abc']), (pin, ['--pin-seq', '-1']), (pin, ['--pin-seq', '']),
               (r0, ['--prefix-start', '0x10', '--prefix-count', 1]),
               (pin, ['--pin-seq-count', 4]), (pin, ['--pin-lt-start', 600000000]),
               (r0, ['--prefix-count', 5])]
        for raw, args in bad:
            with self.subTest(args=args):
                code, log, _hits = emu.run(BINARY, raw, args)
                self.assertNotEqual(code, 0, log)
                self.assertIsNone(report(log))

    def test_slots_closer_than_the_kernel_supports_are_refused(self):
        raw = emu.problem('round0')
        self.assertEqual(raw.count(b'slot 1 406\n'), 1)
        code, log, _ = emu.run(BINARY, raw.replace(b'slot 1 406\n', b'slot 1 405\n'), ['--prefix-start', 0, '--prefix-count', 1])
        self.assertNotEqual(code, 0, log)
        self.assertIsNone(report(log))

    def test_the_whole_last_sequence_value_is_accepted(self):
        # the largest valid start with the largest count that fits: bounds are inclusive where they should be
        code, log, _ = emu.run(BINARY, emu.problem('pin'), ['--pin-seq', 0xFFFFFFFD, '--pin-seq-count', 1,
                                                          '--pin-lt-start', 1699999999, '--pin-lt-count', 1])
        self.assertEqual(code, 0, log)
        self.assertEqual(report(log)['zblocks'], 1)

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
