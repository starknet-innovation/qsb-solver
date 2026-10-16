import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'worker/promotion/validation'))
import fresh_pinning_search as m

class FreshSearchTests(unittest.TestCase):
    def test_intent_blocks_relaunch(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);d=root/'range-00000000';d.mkdir()
            m.save(d/'record.json',{'status':'compute-intent','binding':'b','attempt':0,'workRange':m.work_range('pinning',0)})
            with self.assertRaisesRegex(ValueError,'uncertain'):m.resume_status(root,'b')

    def test_complete_resume_requires_exact_persisted_result(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);d=root/'range-00000000';d.mkdir();m.save(d/'result.json',{'candidates':[]})
            r={'status':'complete','binding':'b','attempt':0,'workRange':m.work_range('pinning',0),'resultSha256':m.sha(d/'result.json')}
            m.save(d/'record.json',r)
            self.assertEqual((1,None),m.resume_status(root,'b'))
            (d/'result.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'changed'):m.resume_status(root,'b')

    def test_partial_directory_blocks(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);(root/'range-00000000').mkdir()
            with self.assertRaisesRegex(ValueError,'Incomplete'):m.resume_status(root,'b')

    def test_every_hit_cpu_verified(self):
        unit=m.work_range('pinning',0);s=unit['sequence'];lt=unit['locktime']
        candidates=[f'sequence={s}\nlocktime={lt}\nsequence={s+1}\nlocktime={lt}\n']
        calls=[]
        def verify(event):
            calls.append(event);seq=s+len(calls)-1
            return {'valid':True,'scriptVersion':m.VERSION,'sequence':seq,'locktime':lt}
        result=m.checked_solution({'request':{}},candidates,unit,verify)
        self.assertEqual({'sequence':s,'locktime':lt},result);self.assertEqual(2,len(calls))
        with self.assertRaisesRegex(ValueError,'rejected'):
            m.checked_solution({'request':{}},candidates,unit,lambda _: {'valid':False})

    def test_outside_range_rejected_before_cpu(self):
        with self.assertRaisesRegex(ValueError,'outside'):
            m.checked_solution({'request':{}},['sequence=1\nlocktime=1\n'],m.work_range('pinning',0),lambda _:self.fail('CPU should not run'))

    def test_real_process_failure_preserves_log(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);binary=root/'fake';binary.write_text('#!/bin/sh\necho partial\nexit 2\n');binary.chmod(0o700)
            with self.assertRaisesRegex(ValueError,'failed'):m.compute(binary,b'public',m.work_range('pinning',0),root,1)
            self.assertEqual('partial\n',(root/'compute.log').read_text())

    def test_real_process_timeout_preserves_log(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);binary=root/'fake';binary.write_text('#!/bin/sh\necho partial\nsleep 10\n');binary.chmod(0o700)
            start=time.monotonic()
            with self.assertRaises(TimeoutError):m.compute(binary,b'public',m.work_range('pinning',0),root,.5)
            self.assertLess(time.monotonic()-start,3);self.assertIn('partial',(root/'compute.log').read_text())

if __name__=='__main__':unittest.main()
