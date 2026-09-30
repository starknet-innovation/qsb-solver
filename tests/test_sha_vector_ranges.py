from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'experiments/generic-sha-vector'))
import run_ranges as m


class RangeTests(unittest.TestCase):
    def receipt(self):
        rows = [dict(name=name, rank=rank, count=count, binary=label, seconds=1,
                     exit=0, timedOut=False, log='[GPU 0] Done enum:', hitFiles={},
                     summary=f'STATUS=EXHAUSTED 1 total_attempts={count} elapsed_s=1 hits=0')
                for name in sorted(m.NAMES) for rank, count in m.RANGES
                for label in ('baseline', 'candidate')]
        return dict(baselineSha256=m.BASELINE, candidateSha256=m.SUB,
                    fixtureSha256=m.FIXTURES, samples=rows)

    def test_complete_inventory(self):
        m.validate(self.receipt())

    def test_wrong_or_partial_evidence_rejects(self):
        for field, value in [('rank', 1), ('count', 0), ('exit', 2), ('hitFiles', {'hit': 'unverified'}),
                             ('summary', 'STATUS=EXHAUSTED 1 total_attempts=0 elapsed_s=1 hits=0')]:
            with self.subTest(field=field):
                r=self.receipt();r['samples'][0][field]=value
                with self.assertRaises(ValueError):m.validate(r)
        r=self.receipt();r['samples'].pop()
        with self.assertRaises(ValueError):m.validate(r)
        r=self.receipt();r['fixtureSha256']='0'*64
        with self.assertRaises(ValueError):m.validate(r)
