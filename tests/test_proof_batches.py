import base64
import copy
import hashlib
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ops/fresh-proof'))
import batches as m

class BatchTests(unittest.TestCase):
    def setUp(self):
        self.runner,self.ranges=m.dependencies()
        self.fixture=dict(network='regtest',requestId='public-request',publicStateJson='{}',manifest={'public':'manifest'})
        self.snapshot=dict(stage='pinning',nextAttempt=0,solutions={},binding=dict(requestId='public-request',manifestHash=hashlib.sha256(m.canonical(self.fixture['manifest']).encode()).hexdigest()))
        self.params=dict(parameterBase64=base64.b64encode(b'public-parameters').decode(),parameterSha256=hashlib.sha256(b'public-parameters').hexdigest())
        self.calls=[]
    def cpu(self,event):self.calls.append(event);return self.params
    def build(self,n=8):return m.build(self.snapshot,self.fixture,self.cpu,n,self.ranges.work_range)
    def test_pinning_uses_progress_and_only_exported_public_parameters(self):
        self.snapshot['nextAttempt']=4;b=self.build();self.runner.validate_batch(b)
        self.assertEqual(b['request']['attempt'],4);self.assertEqual(b['maxAttempts'],8)
        self.assertEqual(b['request']['parameterBase64'],self.params['parameterBase64']);self.assertNotIn('sequence',b['request'])
    def test_subset_uses_durable_verified_pin(self):
        self.snapshot.update(stage='round1',solutions=dict(pinning=dict(valid=True,sequence=2147483648,locktime=500000000)))
        b=self.build();self.assertEqual(b['request']['sequence'],2147483648)
        self.assertEqual(self.calls[0]['locktime'],500000000)
        self.snapshot['solutions']['pinning']['valid']=False
        with self.assertRaises(ValueError):self.build()
    def test_last_domain_batch_is_clipped_without_skips(self):
        self.snapshot.update(stage='round2',nextAttempt=(self.ranges.SUBSET_TOTAL-1)//self.ranges.CHUNK,solutions=dict(pinning=dict(valid=True,sequence=2147483648,locktime=500000000)))
        self.assertEqual(self.build()['maxAttempts'],1)
        self.snapshot['nextAttempt']+=1
        self.calls.clear()
        with self.assertRaisesRegex(ValueError,'exhausted'):self.build()
        self.assertEqual(self.calls,[])
    def test_changed_fixture_or_finished_state_rejects_before_cpu(self):
        for key,value in [('network','mainnet'),('requestId','other'),('manifest',{})]:
            old=self.fixture[key];self.fixture[key]=value
            with self.assertRaises(ValueError):self.build()
            self.fixture[key]=old
        self.snapshot['stage']='solved'
        with self.assertRaises(ValueError):self.build()
        self.assertEqual(self.calls,[])
    def test_invalid_parameter_hash_and_bounds_reject(self):
        for n in [True,0,65]:
            with self.assertRaises(ValueError):self.build(n)
        self.params['parameterSha256']='0'*64
        with self.assertRaisesRegex(ValueError,'parameter'):self.build()
    def test_raw_request_and_canonical_fixture_hashes_are_both_checked(self):
        import tempfile,json
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);request=dict(id='public-request',public='data')
            raw=json.dumps(request,indent=2).encode();(root/'request.json').write_bytes(raw)
            campaign=dict(campaignId='public-request',requestHash=hashlib.sha256(raw).hexdigest())
            fixture=dict(self.fixture,requestSha256=hashlib.sha256(m.canonical(request).encode()).hexdigest())
            data=json.dumps(fixture).encode();(root/'fixture.json').write_bytes(data);digest=hashlib.sha256(data).hexdigest()
            self.assertNotEqual(fixture['requestSha256'],campaign['requestHash'])
            self.assertEqual(m.frozen_fixture(root/'fixture.json',digest,campaign,root/'request.json'),fixture)
            (root/'request.json').write_text(json.dumps(request))
            with self.assertRaisesRegex(ValueError,'byte hash'):m.frozen_fixture(root/'fixture.json',digest,campaign,root/'request.json')
    def test_registration_compares_only_the_supplied_bytes(self):
        import json
        from unittest.mock import patch
        batch=self.build();raw=json.dumps(batch).encode()
        with patch.object(m,'load',side_effect=AssertionError('must not reread a path')):
            self.assertEqual(m.validate_planned(raw,self.snapshot,self.fixture,self.cpu,self.ranges.work_range),batch)
            modified=copy.deepcopy(batch);modified['request']['parameterBase64']='different'
            with self.assertRaisesRegex(ValueError,'modified'):m.validate_planned(json.dumps(modified).encode(),self.snapshot,self.fixture,self.cpu,self.ranges.work_range)
        duplicate=raw[:-1]+b',"maxAttempts":8}'
        with self.assertRaisesRegex(ValueError,'Duplicate'):m.validate_planned(duplicate,self.snapshot,self.fixture,self.cpu,self.ranges.work_range)
