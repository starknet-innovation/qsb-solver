import copy
from pathlib import Path
import sys
import unittest
import tempfile
from unittest.mock import patch
import subprocess
import publish_pqb_tls
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from pqb_tls_probe import accepted_evidence
from pqb_s3_transport_probe import validate_targets

class TransportEvidenceTests(unittest.TestCase):
    def test_rejection_requires_both_live_leaf_observations(self):
        good=dict(expectedLeafSha256='a'*64,observedLeafBeforeSha256='a'*64,
                  observedLeafAfterSha256='a'*64,status='certificate-rejected',verifyCode=20)
        self.assertTrue(accepted_evidence(good))
        for key,value in [('observedLeafBeforeSha256','b'*64),('observedLeafAfterSha256','b'*64),
                          ('observedLeafBeforeSha256',None),('verifyCode',10),('status','inconclusive')]:
            self.assertFalse(accepted_evidence({**good,key:value}))

    def spec(self):
        url='https://public-fixture.s3.eu-west-2.amazonaws.com/a%20b/test.json?X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Credential=PUBLIC/20261112/eu-west-2/s3/aws4_request&X-Amz-Signature=abc'
        return dict(bucket='public-fixture',region='eu-west-2',key='a b/test.json',putUrl=url,getUrl=url)

    def test_urls_bind_both_operations_to_region_bucket_and_key(self):
        self.assertTrue(validate_targets(self.spec())['validated'])
        for field in ['putUrl','getUrl']:
            for before,after in [('https:','http:'),('public-fixture.s3.','other.s3.'),
                ('/a%20b/test.json','/other.json'),('amazonaws.com/','amazonaws.com:444/'),
                ('/eu-west-2/s3/','/eu-west-1/s3/'),('amazonaws.com/','amazonaws.com.attacker.test/'),
                ('public-fixture.s3.','user@public-fixture.s3.')]:
                changed=copy.deepcopy(self.spec());changed[field]=changed[field].replace(before,after)
                with self.subTest(field=field,before=before),self.assertRaises(ValueError):validate_targets(changed)
        for key,value in [('bucket','other'),('region','eu-west-1'),('key','other.json')]:
            with self.subTest(key=key),self.assertRaises(ValueError):validate_targets({**self.spec(),key:value})

    def test_existing_release_cannot_be_republished(self):
        with tempfile.TemporaryDirectory() as tmp, \
             patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],0,b'',b'')), \
             patch.object(publish_pqb_tls,'run') as mutate:
            with self.assertRaisesRegex(ValueError,'already exists'):
                publish_pqb_tls.main(Path(tmp)/'attempt')
            mutate.assert_not_called()
