import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research/pqb-ranked/measure'))
import qualify_all as q


class AllUnitsTests(unittest.TestCase):
    def test_all_units_are_separate_and_one_shot(self):
        with tempfile.TemporaryDirectory() as tmp:
            calls=[]
            def runner(gate,result,stage):
                calls.append(stage);result.mkdir();(result/'result.json').write_text('{"status":"passed"}')
                return dict(status='passed')
            out=Path(tmp)/'new'
            result=q.run(tmp,out,4000,runner=runner,now=lambda:0)
            self.assertEqual(result['status'],'passed');self.assertEqual(calls,list(q.STAGES))
            with self.assertRaises(FileExistsError):q.run(tmp,out,4000,runner=runner,now=lambda:0)

    def test_failed_unit_or_deadline_margin_stops_further_compute(self):
        with tempfile.TemporaryDirectory() as tmp:
            calls=[]
            def runner(gate,result,stage):
                calls.append(stage);result.mkdir();(result/'result.json').write_text('{"status":"failed"}')
                return dict(status='failed')
            self.assertEqual(q.run(tmp,Path(tmp)/'failed',4000,runner=runner,now=lambda:0)['status'],'failed')
            self.assertEqual(calls,['pinning']);calls.clear()
            self.assertEqual(q.run(tmp,Path(tmp)/'deadline',1000,runner=runner,now=lambda:0)['status'],'failed')
            self.assertEqual(calls,[])
