import importlib.util
from pathlib import Path
import unittest
import copy
spec=importlib.util.spec_from_file_location('fresh',Path(__file__).resolve().parents[1]/'worker/promotion/validation/run_fresh_batch.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class FreshBatchTests(unittest.TestCase):
    def setUp(self):
        self.batch={'batchId':'00000000-0000-4000-8000-000000000001','request':{'kernelCommit':m.COMMIT,'stage':'pinning','attempt':0,'manifestHash':'a'*64},'maxAttempts':4}
        self.snapshots=[]
    def ranges(self,stage,attempt):return {'start':str(attempt*10),'count':10}
    def result(self,event):
        d=event['input'];return {**d,'status':'completed','checkpoint':'range-complete','workRange':self.ranges(d['stage'],d['attempt']),'candidates':[]}
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
            if mode=='failed':self.assertEqual(m.run_batch(self.batch,fail,self.ranges,self.publish)['status'],'failed')
            else:
                with self.assertRaises(ValueError):m.run_batch(self.batch,fail,self.ranges,self.publish)
    def test_private_fields_and_unbounded_counts_reject(self):
        self.batch['request']['privateKeyHex']='forbidden'
        with self.assertRaises(ValueError):m.validate_batch(self.batch)
        del self.batch['request']['privateKeyHex'];self.batch['maxAttempts']=65
        with self.assertRaises(ValueError):m.validate_batch(self.batch)
    def test_no_attempt_starts_without_timeout_reserve(self):
        values=iter([0,600])
        result=m.run_batch(self.batch,self.result,self.ranges,self.publish,clock=lambda:next(values))
        self.assertEqual(result['results'],[]);self.assertEqual(result['status'],'bounded-stop')
