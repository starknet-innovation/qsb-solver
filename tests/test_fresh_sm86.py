import importlib.util
from pathlib import Path
import unittest
import copy
spec=importlib.util.spec_from_file_location('fresh',Path(__file__).resolve().parents[1]/'worker/promotion/validation/run_fresh_sm86.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class FreshSm86Tests(unittest.TestCase):
    def setUp(self):
        self.batch={'batchId':'00000000-0000-4000-8000-000000000001','request':{'kernelCommit':m.COMMIT,'stage':'pinning','attempt':0,'manifestHash':'a'*64},'maxAttempts':4}
        self.snapshots=[]
    def ranges(self,stage,attempt):return {'start':str(attempt*10),'count':10}
    def result(self,event):
        d=event['input'];return {**d,'status':'completed','checkpoint':'range-complete','workRange':self.ranges(d['stage'],d['attempt']),'candidates':[],'verified':False}
    def publish(self,s):self.snapshots.append(copy.deepcopy(s))
    def test_progress_published_before_and_after_each_attempt(self):
        final=m.run_batch(self.batch,self.result,self.ranges,self.publish)
        self.assertEqual([x['attempt'] for x in final['results']],list(range(4)))
        self.assertEqual(final['status'],'batch-complete')
        self.assertEqual(self.snapshots[1]['activeAttempt'],0)
    def test_candidate_stops_without_automatic_verification(self):
        def hit(e):r=self.result(e);r['candidates']=['public-hit'];return r
        result=m.run_batch(self.batch,hit,self.ranges,self.publish)
        self.assertEqual(len(result['results']),1);self.assertEqual(result['status'],'candidate')
        self.assertTrue(result['candidateRequiresCpuVerification'])
    def test_failure_or_identity_mismatch_never_advances(self):
        for mode in ['failed','wrong-range']:
            def fail(e):
                r=self.result(e)
                if mode=='failed':r['status']='failed';r['checkpoint']='requires-verification-or-resume'
                else:r['workRange']={}
                return r
            result=m.run_batch(self.batch,fail,self.ranges,self.publish)
            self.assertEqual(result['status'],'operator-reconciliation-required')
            self.assertEqual(result['activeAttempt'],0)
            self.assertEqual(result['results'],[])
    def test_private_fields_and_unbounded_counts_reject(self):
        self.batch['request']['privateKeyHex']='forbidden'
        with self.assertRaises(ValueError):m.validate_batch(self.batch)
        del self.batch['request']['privateKeyHex'];self.batch['maxAttempts']=65
        with self.assertRaises(ValueError):m.validate_batch(self.batch)
    def test_no_attempt_starts_without_timeout_reserve(self):
        values=iter([0,600])
        result=m.run_batch(self.batch,self.result,self.ranges,self.publish,clock=lambda:next(values))
        self.assertEqual(result['results'],[]);self.assertEqual(result['status'],'bounded-stop')

    def test_malformed_completed_result_is_not_credited(self):
        for value in [None, 'public-hit']:
            def malformed(e):
                result=self.result(e);result['candidates']=value;return result
            self.assertEqual(m.run_batch(self.batch,malformed,self.ranges,self.publish)['status'], 'operator-reconciliation-required')
            self.assertEqual(self.snapshots[-1]['results'],[])

    def test_full_call_reserve_boundary(self):
        for elapsed, expected in [(40,1),(41,0)]:
            self.batch['maxAttempts']=1
            values=iter([0,elapsed,elapsed])
            result=m.run_batch(self.batch,self.result,self.ranges,self.publish,clock=lambda:next(values))
            self.assertEqual(len(result['results']),expected)
            self.assertFalse(result['grantsRangeCredit'])

    def test_exception_preserves_completed_and_uncertain_attempt(self):
        def invoke(e):
            if e['input']['attempt']==1:raise TimeoutError('uncertain')
            return self.result(e)
        result=m.run_batch(self.batch,invoke,self.ranges,self.publish)
        self.assertEqual(len(result['results']),1)
        self.assertEqual(result['activeAttempt'],1)
        self.assertEqual(result['status'],'operator-reconciliation-required')

    def test_checkpoint_failure_prevents_invoke(self):
        calls=[]
        def publish(state):
            if state['activeAttempt'] is not None:raise OSError('disk full')
        with self.assertRaises(OSError):
            m.run_batch(self.batch,lambda e:calls.append(e),self.ranges,publish)
        self.assertEqual(calls,[])

    def test_frozen_binding(self):
        binding=dict(solverCommit=m.COMMIT,architecture='sm_86',files=dict(pinning=m.PIN,subset=m.SUB))
        m.validate_binding(binding)
        for key,value in [('solverCommit','a'*40),('architecture','sm_89'),('files',{})]:
            with self.assertRaises(ValueError):m.validate_binding(dict(binding,**{key:value}))

    def test_atomic_checkpoint_replacement(self):
        import tempfile
        import json
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'result.json'
            m.write_checkpoint(p,{'activeAttempt':1})
            m.write_checkpoint(p,{'activeAttempt':None})
            self.assertIsNone(json.loads(p.read_text())['activeAttempt'])
            self.assertFalse(p.with_suffix('.tmp').exists())

    def test_host_timeout_and_isolation(self):
        root=Path(__file__).resolve().parents[1]
        host=(root/'ops/aws-gpu-execution/host-a10g-fresh.sh').read_text()
        self.assertIn('-ge 1020',host)
        self.assertIn('960 docker run',host)
        self.assertIn('--network none --read-only --cap-drop ALL',host)
        self.assertIn('docker rm --force qsb-a10g-fresh',host)
        self.assertIn('@sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d',host)

    def test_entrypoint_rejects_existing_intent_before_compute(self):
        import tempfile
        import json
        import sys
        from types import SimpleNamespace
        from unittest.mock import patch, Mock
        fake=SimpleNamespace(
            release_binding=lambda:dict(solverCommit=m.COMMIT,architecture='sm_86',
                                         files=dict(pinning=m.PIN,subset=m.SUB)),
            historical_handler=SimpleNamespace(validate_request=lambda r:None),
            handler=Mock())
        with tempfile.TemporaryDirectory() as d:
            batch=Path(d)/'batch.json'; batch.write_text(json.dumps(self.batch))
            target=Path(d)/'result.json'; target.write_text('{"status":"intent"}')
            with patch.dict(sys.modules,handler=fake,search_ranges=SimpleNamespace(work_range=self.ranges)), \
                 patch.object(sys,'argv',['runner',str(batch),str(target)]), \
                 patch('subprocess.check_output',return_value='NVIDIA A10G'):
                with self.assertRaises(FileExistsError):m.main()
            fake.handler.assert_not_called()
            self.assertEqual(json.loads(target.read_text()),{'status':'intent'})

    def test_slow_checkpoint_cannot_consume_call_reserve(self):
        values=iter([0,0,41])
        calls=[]
        result=m.run_batch(self.batch,lambda e:calls.append(e),self.ranges,self.publish,
                           clock=lambda:next(values))
        self.assertEqual(calls,[])
        self.assertEqual(result['status'],'bounded-stop')
        self.assertEqual(result['neverStartedAttempt'],0)
        self.assertIsNone(result['activeAttempt'])
        self.assertEqual(result['results'],[])
