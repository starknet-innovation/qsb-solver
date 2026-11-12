"""Check retained review completeness and measured mitigation, without network or GPU work."""
import collections
import hashlib
import json
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from pqb_descriptor import evidence_bytes


class CriticalReviewTests(unittest.TestCase):
    def test_all_original_critical_matches_have_a_bound_decision(self):
        root=ROOT/'docs/pqb/evidence/critical-review-2026-11-12'
        manifest=json.loads((root/'manifest.json').read_bytes())
        entries={r['path']:r for r in manifest['files']}
        self.assertEqual(len(entries),len(manifest['files']))
        self.assertEqual(set(entries),{str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name!='manifest.json'})
        for name,row in entries.items():evidence_bytes(root,name,row)
        review=json.loads((root/'review.json').read_bytes())
        scan=ROOT/'docs/pqb/evidence/final-image-2026-11-12/build/image-scan/image-scan.json'
        self.assertEqual(hashlib.sha256(scan.read_bytes()).hexdigest(),review['scanSummarySha256'])
        key=lambda r:(r['id'],r['package'],r['version'])
        self.assertEqual(collections.Counter(map(key,json.loads(scan.read_bytes())['unfixedCritical'])),
                         collections.Counter(map(key,review['findings'])))
        self.assertEqual(len(review['findings']),20)
        self.assertEqual(sum(r['disposition']=='release-blocker' for r in review['findings']),4)
        self.assertEqual(review['decision'],'BLOCK-PUBLICATION')
        self.assertFalse(review['publicationVerified']);self.assertFalse(review['enrolled'])
        preparation=json.loads((root/'enrollment-preparation.json').read_bytes())
        self.assertEqual(preparation['pullRequest'],150)
        self.assertFalse(preparation['registryChanged'])

    def test_original_and_proposed_trust_results_are_not_conflated(self):
        root=ROOT/'docs/pqb/evidence/critical-review-2026-11-12'
        original=json.loads((root/'live-tls-check.json').read_bytes())['results']
        proposed=json.loads((root/'live-system-tls-check.json').read_bytes())['results']
        self.assertEqual(original[0]['status'],'accepted');self.assertEqual(proposed[0]['status'],'accepted')
        self.assertEqual(len(original[1:]),14);self.assertEqual(len(proposed[1:]),14)
        accepted=[r for r in original[1:] if r['status']=='accepted']
        self.assertEqual(len(accepted),7)
        self.assertTrue(all(r['leafMatchesPublishedChain'] for r in accepted))
        self.assertTrue(all(r['status']=='certificate-rejected' for r in proposed[1:]))
        overlay=json.loads((root/'overlay-regression.json').read_bytes())
        self.assertEqual([r['returnCode'] for r in overlay],[1,0])
        self.assertEqual(overlay[1]['entrypointSha256'],hashlib.sha256((ROOT/'worker/aws/entrypoint.py').read_bytes()).hexdigest())
        fixtures=ROOT/'tests/fixtures/aws-tls'
        provenance=json.loads((fixtures/'provenance.json').read_bytes())
        self.assertEqual(len(provenance['chains']),16)
        for row in provenance['chains']+[provenance['positiveControl']]:
            self.assertEqual(hashlib.sha256((fixtures/row['path']).read_bytes()).hexdigest(),row['sha256'])
