"""Validate retained native/build identities; never launches hardware or credits new work."""
import json
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from pqb_descriptor import evidence_bytes, sha, source
from check_pqb_final import native_rows
from verify_pqb_build import verify_policy


class FinalEvidenceTests(unittest.TestCase):
    def test_final_artifact_and_original_native_receipts_are_bound(self):
        root=ROOT/'docs/pqb/evidence/final-image-2026-11-12'
        manifest=json.loads((root/'manifest.json').read_bytes())
        entries={r['path']:r for r in manifest['files']}
        self.assertEqual(len(entries),len(manifest['files']))
        actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name!='manifest.json'}
        self.assertEqual(actual,set(entries))
        for name,row in entries.items():evidence_bytes(root,name,row)
        def read(name):return json.loads(evidence_bytes(root,name,entries[name]))
        proposal=read('release/descriptor-proposal.json')
        self.assertEqual(proposal['status'],'HOLD')
        self.assertFalse(proposal['publicationVerified'])
        self.assertFalse(manifest['registryPublicationVerified'])
        self.assertFalse(manifest['enrolled']);self.assertFalse(manifest['deployed'])
        build={key:read('build/'+name) for key,name in (
            ('identity','oci-identity.json'),('config','image-config.json'),
            ('binding','binding.json'),('receipt','build-receipt.json'))}
        self.assertEqual(sha((root/'build/image-manifest.json').read_bytes()),build['identity']['imageDigest'][7:])
        self.assertEqual(manifest['image'],build['identity'])
        self.assertEqual((root/'release/pqb-ranked-v2.json').read_bytes(),
                         source(manifest['imageSourceCommit'],'contracts/pqb-ranked-v2.json'))
        raw=evidence_bytes(root,'native/public-result.json.gz',entries['native/public-result.json.gz'])
        rows=native_rows(raw,manifest['nativeArchive']['sha256'],proposal['solver'],build)
        self.assertEqual([r['stage'] for r in rows],['pinning','round0','round1'])
        consumer=read('verification/final-consumer.json')
        self.assertEqual(consumer['status'],'passed')
        self.assertEqual(consumer['archiveSha256'],sha(raw))
        self.assertEqual(consumer['proposalSha256'],sha((root/'release/descriptor-proposal.json').read_bytes()))
        self.assertEqual(consumer['consumerCommit'],manifest['consumerCommit'])
        self.assertEqual(sum(r['consumerChecks']['checked'] for r in consumer['stages']),1)
        self.assertEqual(sum(r['consumerChecks']['canonicalRechecks'] for r in consumer['stages']),1)
        for name in ['SHA256SUMS','image.oci.tar','image-manifest.json']:
            verify_policy(read('verification/'+name+'.verification.json'),manifest['imageSourceCommit'],
                          'refs/heads/codex/pqb-qualify-20261112',manifest['originalOciArchive']['githubRunId'])

    def test_independent_cleanup_is_complete_and_reservations_released(self):
        root=ROOT/'docs/pqb/evidence/final-image-2026-11-12'
        closeout=json.loads((root/'cloud/campaign-closeout.json').read_bytes())
        self.assertTrue(closeout['reservationReleased'])
        self.assertEqual(closeout['unknownSubmissions'],[])
        self.assertTrue(all(r['reservationReleased'] for r in closeout['sessions']))
        result=json.loads((root/'cloud/reconciliation-final.json').read_bytes())['structuredContent']
        self.assertEqual(result['status'],'success')
        self.assertEqual(len(result['api_calls']),14)
        self.assertTrue(all(c['status']=='success' for c in result['api_calls']))
        data=result['return_value'];self.assertFalse(data['errors'])
        self.assertTrue(all(not value for value in data['pagination'].values()))
        for name,value in data['resources'].items():
            if name.endswith(':instances'):
                self.assertTrue(all(i['State']['Name']=='terminated' for r in value['Reservations'] for i in r['Instances']))
            else:
                self.assertTrue(all(not v for v in value.values()),name)
