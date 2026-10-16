import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from types import SimpleNamespace

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
            root=Path(t);d=root/'range-00000000';d.mkdir();(d/'compute.log').write_text('Done:')
            m.save(d/'result.json',{'candidates':[],'logSha256':m.sha(d/'compute.log')})
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

    def test_prepare_execute_once_and_next_attempt(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);(root/'public.json').write_text('{}');(root/'hashes.json').write_text('{}')
            args=SimpleNamespace(output=root/'out',binary=root/'binary',reference=root/'reference',
                reference_hashes=root/'hashes.json',public=root/'public.json',binary_sha256='a'*64,
                intent_ack_dir=root/'acks',deadline=int(time.time())+3600,range_timeout=1,mode='prepare',attempt=None)
            def compute(binary,raw,unit,directory,timeout):
                (directory/'compute.log').write_text('Done:')
                return {'candidates':[],'logSha256':m.sha(directory/'compute.log')}
            with patch.object(m,'verify_artifacts'),patch.object(m,'verify_public',return_value=b'public'),patch.object(m.subprocess,'check_output',return_value='GPU-test'),patch.object(m,'await_intent_ack'),patch.object(m,'compute',side_effect=compute) as process:
                self.assertEqual('prepared',m.run(args)['status']);process.assert_not_called()
                with self.assertRaisesRegex(ValueError,'uncertain'):m.run(args)
                args.mode='execute';args.attempt=0
                self.assertEqual('complete',m.run(args)['status']);self.assertEqual(1,process.call_count)
                with self.assertRaisesRegex(ValueError,'unexecuted'):m.run(args)
                self.assertEqual(1,process.call_count)
                args.mode='prepare'
                self.assertEqual(1,m.run(args)['attempt']);self.assertEqual(1,process.call_count)

    def test_ack_exact_binding_or_fail_closed(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);record=root/'record.json';record.write_text('{}');acks=root/'acks';acks.mkdir()
            with self.assertRaisesRegex(TimeoutError,'compute refused'):m.await_intent_ack(record,acks,'b',0,.01)
            ack=acks/'b-00000000.json';ack.write_text('{}')
            with self.assertRaisesRegex(ValueError,'mismatch'):m.await_intent_ack(record,acks,'b',0,.01)
            m.save(ack,{'recordPath':'range-00000000/record.json','recordSha256':m.sha(record),'binding':'b'})
            m.await_intent_ack(record,acks,'b',0,.01)

    def test_real_process_failure_preserves_log(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);binary=root/'fake';binary.write_text('#!/bin/sh\necho partial\nexit 2\n');binary.chmod(0o700)
            with self.assertRaisesRegex(ValueError,'failed'):m.compute(binary,b'public',m.work_range('pinning',0),root,1)
            self.assertEqual('partial\n',(root/'compute.log').read_text())

    def test_real_process_timeout_preserves_log(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);binary=root/'fake';binary.write_text('#!/bin/sh\necho partial\nsleep 10\n');binary.chmod(0o700)
            start=time.monotonic()
            with self.assertRaisesRegex(RuntimeError,"stopped"):m.compute(binary,b'public',m.work_range('pinning',0),root,.5)
            self.assertLess(time.monotonic()-start,3);self.assertIn('partial',(root/'compute.log').read_text())

if __name__=='__main__':unittest.main()
