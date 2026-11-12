import copy
from pathlib import Path
import sys
import unittest
import tempfile
from unittest.mock import patch
import subprocess
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import publish_pqb_tls
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

    def test_retained_archive_parts_require_complete_bytes_and_signed_whole_hash(self):
        import hashlib,json
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);chunks=[b'abc',b'def'];expected=hashlib.sha256(b''.join(chunks)).hexdigest()
            rows=[]
            for i,data in enumerate(chunks,1):
                name=f'image.oci.tar.part-{i:02d}';(root/name).write_bytes(data)
                rows.append(dict(file=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
            parts=dict(archiveSha256=expected,parts=rows)
            publish_pqb_tls.verify_archive_parts(root,parts,expected)
            (root/rows[0]['file']).write_bytes(b'xbc')
            with self.assertRaises(ValueError):publish_pqb_tls.verify_archive_parts(root,parts,expected)
            (root/rows[0]['file']).write_bytes(chunks[0])
            for changed in [dict(archiveSha256='0'*64,parts=rows),dict(archiveSha256=expected,parts=rows[:1]),
                            dict(archiveSha256=expected,parts=[rows[0],rows[0]]),
                            dict(archiveSha256=expected,parts=[{**rows[0],'file':'../outside'},rows[1]])]:
                with self.assertRaises(ValueError):publish_pqb_tls.verify_archive_parts(root,changed,expected)
            (root/rows[1]['file']).unlink()
            with self.assertRaises(ValueError):publish_pqb_tls.verify_archive_parts(root,parts,expected)

    def test_final_tag_is_idempotent_and_only_explicitly_repairs_a_missing_tag(self):
        import hashlib
        payload=b'qualified-index';digest='sha256:'+hashlib.sha256(payload).hexdigest()
        with tempfile.TemporaryDirectory() as tmp, patch.object(publish_pqb_tls,'DIGEST',digest), \
             patch.object(publish_pqb_tls,'run') as mutate, \
             patch.object(publish_pqb_tls,'capture',return_value=payload):
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],0,payload,b'')):
                publish_pqb_tls.final_tag(Path(tmp),repair=True)
            mutate.assert_not_called()
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],0,b'other',b'')):
                with self.assertRaisesRegex(ValueError,'refuse overwrite'):publish_pqb_tls.final_tag(Path(tmp),repair=True)
            mutate.assert_not_called()
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],1,b'',b'manifest unknown')):
                with self.assertRaisesRegex(ValueError,'finalize-published'):publish_pqb_tls.final_tag(Path(tmp))
                mutate.assert_not_called()
                publish_pqb_tls.final_tag(Path(tmp),repair=True)
                mutate.assert_called_once()
            mutate.reset_mock()
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],1,b'',b'connection failed')):
                with self.assertRaises(subprocess.CalledProcessError):publish_pqb_tls.final_tag(Path(tmp),repair=True)
            mutate.assert_not_called()

    def test_reviewed_inventory_rejects_omissions_duplicates_traversal_and_symlinks(self):
        import hashlib,json
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);payload=b'public evidence';(root/'receipt').write_bytes(payload)
            row=dict(path='receipt',bytes=len(payload),sha256=hashlib.sha256(payload).hexdigest())
            def manifest(rows): (root/'manifest.json').write_text(json.dumps(dict(files=rows)))
            manifest([row]);publish_pqb_tls.reviewed_inventory(root)
            (root/'unlisted-operator-file').write_bytes(b'public synthetic placeholder')
            with self.assertRaisesRegex(ValueError,'inventory'):publish_pqb_tls.reviewed_inventory(root)
            (root/'unlisted-operator-file').unlink()
            manifest([row,row])
            with self.assertRaisesRegex(ValueError,'Duplicate'):publish_pqb_tls.reviewed_inventory(root)
            manifest([{**row,'path':'../receipt'}])
            with self.assertRaisesRegex(ValueError,'Unsafe'):publish_pqb_tls.reviewed_inventory(root)
            manifest([row]);(root/'link').symlink_to(root/'receipt')
            with self.assertRaisesRegex(ValueError,'symlink'):publish_pqb_tls.reviewed_inventory(root)

    def test_release_git_tag_must_resolve_to_the_qualified_commit(self):
        import json
        commit=dict(object=dict(type='commit',sha=publish_pqb_tls.NEW))
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],0,json.dumps(commit).encode(),b'')):
                self.assertEqual(publish_pqb_tls.release_git_tag(root),publish_pqb_tls.NEW)
            wrong=dict(object=dict(type='commit',sha='a'*40))
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],0,json.dumps(wrong).encode(),b'')):
                with self.assertRaisesRegex(ValueError,'differs'):publish_pqb_tls.release_git_tag(root)
            annotated=dict(object=dict(type='tag',sha='b'*40))
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],0,json.dumps(annotated).encode(),b'')), \
                 patch.object(publish_pqb_tls,'capture',return_value=json.dumps(commit).encode()):
                self.assertEqual(publish_pqb_tls.release_git_tag(root),publish_pqb_tls.NEW)
            with patch.object(publish_pqb_tls.subprocess,'run',return_value=subprocess.CompletedProcess([],1,b'',b'HTTP 404')):
                self.assertIsNone(publish_pqb_tls.release_git_tag(root,allow_absent=True))
                with self.assertRaises(subprocess.CalledProcessError):publish_pqb_tls.release_git_tag(root)
