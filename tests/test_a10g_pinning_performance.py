import copy
import sys
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'worker/promotion/validation'))
import run_a10g_pinning_performance as m

class PinningPerformanceTests(unittest.TestCase):
    def setUp(self):
        self.row=dict(arguments=m.ARGS,count=m.COUNT,seconds=5,exit=0,timedOut=False,hitFiles={},paramsSha256='a'*64,
            log='=== Search: lt=[500000000,1744600000] (256000000), seq=[0x80000000+], GPU 0 (global 0 of 1) ===\n  Done: 256M in 5s (51.2M/s), found=0\n')
        self.result=dict(baselineSha256=m.BASELINE,candidateSha256=m.CANDIDATE,samples=[dict(self.row,name=n,sample=i,binary=b)
            for n in sorted(m.NAMES) for i in range(3) for b in (('baseline','candidate') if i%2==0 else ('candidate','baseline'))])
    def test_complete(self):self.assertEqual(len(m.summarize(self.result)),2)
    def test_reject_shortened_failed_hit_wrong_bounds(self):
        for row in (dict(self.row,exit=2),dict(self.row,timedOut=True),dict(self.row,hitFiles={'hit':'public'}),dict(self.row,arguments=[]),dict(self.row,log=self.row['log'].replace('256M','255M')),dict(self.row,log=self.row['log']*2)):
            with self.assertRaises(ValueError):m.check(row)
    def test_reject_incomplete_or_changed_parameters(self):
        bad=copy.deepcopy(self.result);bad['samples'][0]['paramsSha256']='b'*64
        for r in (bad,dict(self.result,samples=self.result['samples'][:-1]),dict(self.result,baselineSha256='0'*64)):
            with self.assertRaises(ValueError):m.summarize(r)
    def test_projection_rejects_timeout(self):
        bad=copy.deepcopy(self.result)
        for row in bad['samples']:row['seconds']=20
        with self.assertRaisesRegex(ValueError,'worker timeout'):m.summarize(bad)
