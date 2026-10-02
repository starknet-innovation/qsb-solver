import math
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'experiments/generic-sha-vector'))
from run_trace import unrank,trace_records

class TraceRecordTests(unittest.TestCase):
    def line(self, rank, bit):
        return 'TRACE_SUB indices='+','.join(map(str,unrank(rank)))+f' recid={bit} hash='+('ab'*32)
    def test_domain_edges(self):
        self.assertEqual(unrank(0),tuple(range(9)))
        self.assertEqual(unrank(math.comb(150,9)-1),tuple(range(141,150)))
        for bad in [-1,math.comb(150,9)]:
            with self.assertRaises(ValueError):unrank(bad)
    def test_complete_trace_and_rejections(self):
        lines=[self.line(rank,bit) for rank in range(63,65) for bit in (0,1)]
        self.assertEqual(len(trace_records('\n'.join(reversed(lines)),63,2)),4)
        for bad in [lines[:-1],lines+lines[:1],lines[:-1]+[self.line(65,1)],lines[:-1]+['TRACE_SUB broken']]:
            with self.assertRaises(ValueError):trace_records('\n'.join(bad),63,2)
