import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import unittest
import test_proof_results as fixtures
from test_proof_results import r,s,ROOT
sys.path.insert(0,str(ROOT/'ops/fresh-proof'))
spec=importlib.util.spec_from_file_location('proof_verify',ROOT/'ops/fresh-proof/verify.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
spec=importlib.util.spec_from_file_location('membership',ROOT/'worker/promotion/validation/candidate_range.py')
membership=importlib.util.module_from_spec(spec);spec.loader.exec_module(membership)

class CpuPublicationTests(unittest.TestCase):
    def setUp(self):
        f=fixtures.ResultsTests();f.setUp();self.batch=f.batch;self.files=f.files
        self.fixture=dict(network='regtest',requestId=self.batch['batchId'],publicStateJson='{}',manifest={'public':'fixture'})
        self.params=dict(parameterBase64='public',parameterSha256='b'*64)
        self.batch['request'].update(protocol='qsb-config-a-v1',searchVersion='ranked-v2',**self.params)
        self.batch['request']['manifestHash']=hashlib.sha256(m.canonical(self.fixture['manifest']).encode()).hexdigest()
        self.state=json.loads(self.files['result.json']);self.state['request']=self.batch['request']
        self.state['results'][0]['manifestHash']=self.batch['request']['manifestHash']
        self.calls=[];self.verdict=dict(valid=True,sequence=2147483648,locktime=500000000)
    def cpu(self,event):
        self.calls.append(event)
        return self.params if event['action']=='export' else self.verdict
    def run_check(self):
        raw=json.dumps(self.batch).encode();self.state['batchSha256']=hashlib.sha256(raw).hexdigest()
        self.files['result.json']=json.dumps(self.state)
        return m.verify(self.files,raw,self.fixture,self.cpu,r.validate_batch,r.validate_binding,s.work_range,membership.validate_candidates_in_range)
    def hit(self):
        self.state.update(status='candidate',candidateRequiresCpuVerification=True)
        self.state['results'][0]['candidates']=['sequence=2147483648\nlocktime=500000000\n']
    def test_empty_range_cpu_bound_but_no_direct_credit(self):
        result=self.run_check();self.assertTrue(result['rows'][0]['wholeRangeEligible'])
        self.assertFalse(result['grantsRangeCredit']);self.assertEqual(len(self.calls),1)
    def test_hit_is_verified_but_never_whole_range_credit(self):
        self.hit();result=self.run_check()
        self.assertEqual(result['verifiedSolution'],self.verdict)
        self.assertFalse(result['rows'][0]['wholeRangeEligible'])
        self.assertTrue(result['requiresCandidateReconciliation'])
    def test_der_only_hit_never_advances(self):
        self.hit();self.verdict=dict(valid=False,derOnly=True)
        result=self.run_check();self.assertIsNone(result['verifiedSolution'])
        self.assertFalse(result['rows'][0]['wholeRangeEligible']);self.assertNotIn('nextAttempt',result)
    def test_unexpected_rejection_fails_closed(self):
        self.hit();self.verdict=dict(valid=False)
        with self.assertRaisesRegex(ValueError,'CPU-rejected'):self.run_check()
    def test_out_of_range_candidate_rejected_before_cpu_verify(self):
        self.hit();self.state['results'][0]['candidates']=['sequence=2147483664\nlocktime=500000000\n']
        with self.assertRaisesRegex(ValueError,'outside'):self.run_check()
        self.assertEqual(len(self.calls),1)
    def test_wrong_parameter_export_rejects(self):
        self.params=dict(parameterBase64='different',parameterSha256='0'*64)
        with self.assertRaisesRegex(ValueError,'parameters differ'):self.run_check()
    def test_changed_manifest_rejected_before_cpu(self):
        self.fixture['manifest']['public']='changed'
        with self.assertRaisesRegex(ValueError,'manifest'):self.run_check()
        self.assertEqual(self.calls,[])
    def test_uncertain_execution_rejected_before_cpu(self):
        self.state.update(status='running',activeAttempt=1);self.files['exit-code.txt']='124'
        with self.assertRaisesRegex(ValueError,'uncertain'):self.run_check()
        self.assertEqual(self.calls,[])
    def test_mainnet_fixture_rejected(self):
        self.fixture['network']='mainnet'
        with self.assertRaisesRegex(ValueError,'chain'):self.run_check()
    def test_changed_cpu_reference_cannot_execute(self):
        import tempfile
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as directory:
            source=Path(directory)
            for name in m.REFERENCE:(source/name).write_text('untrusted')
            with patch('subprocess.run') as run:
                with self.assertRaisesRegex(ValueError,'reference changed'):
                    m.CpuReference(source)({'action':'export'})
                run.assert_not_called()
    def test_subset_requires_pin_context(self):
        self.batch['request']['stage']='round1';self.state['results'][0]['stage']='round1'
        self.state['results'][0]['workRange']=s.work_range('round1',0)
        with self.assertRaisesRegex(ValueError,'pin context'):self.run_check()
        self.assertEqual(self.calls,[])
    def test_cli_rejects_tampered_evidence_before_cpu(self):
        import base64,gzip,tempfile
        from unittest.mock import patch
        import results
        self.run_check()
        raw=json.dumps(self.batch).encode()
        encoded=base64.b64encode(gzip.compress(json.dumps(self.files).encode()))
        meta=dict(bytes=len(encoded),sha256=hashlib.sha256(encoded).hexdigest())
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);evidence=root/'evidence'
            results.persist_collection(evidence,encoded,meta,raw,r.validate_batch,r.validate_binding,s.work_range)
            fixture=root/'fixture.json';fixture.write_text(json.dumps(self.fixture))
            (evidence/'result.json').write_text('{}')
            argv=['verify','--collection',str(evidence),'--fixture',str(fixture),
                  '--fixture-sha256',hashlib.sha256(fixture.read_bytes()).hexdigest(),
                  '--reference',str(root/'reference'),'--output',str(root/'receipt.json')]
            with patch.object(sys,'argv',argv),patch.object(m,'CpuReference') as cpu:
                with self.assertRaisesRegex(ValueError,'evidence changed'):m.main()
                cpu.assert_not_called()
            self.assertFalse((root/'receipt.json').exists())
