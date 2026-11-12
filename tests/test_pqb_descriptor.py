"""Release identity failures must not turn an unrelated image into a PQB proposal."""
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from pqb_descriptor import ROOT, contract_hash, prepare, sha, source

EVIDENCE = ROOT / 'docs/pqb/evidence/public-transport-2026-11-11'
REVIEW = 'b0ea0147eb6680b9e16e1a69129307ebe2f0339b'


class PqbDescriptorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.value = prepare(EVIDENCE, REVIEW)

    def test_real_receipts_remain_hold_and_source_bound(self):
        p = self.value
        self.assertEqual(p['status'], 'HOLD')
        self.assertFalse(p['publicationVerified'])
        self.assertFalse(p['enrollmentApproved'])
        self.assertEqual(p['solver']['protocol'], 'pqb-v1')
        self.assertEqual(p['solver']['kernelCommit'], p['solver']['solverCommit'])
        self.assertEqual(p['solver']['searchContract'], '5217daa6415b83dcce2d85159130df4994ab0e9bb67910c7bdf00e5804f4ee71')
        self.assertEqual({x['path'] for x in p['binding']['runtimeInputDrift']},
                         {'worker/pqb/pqb_handler.py', 'worker/pqb/build.py'})
        self.assertEqual(p['binding']['evidenceFilesChecked'], 79)

    def test_contract_vectors_and_float_token_are_checked(self):
        commit = self.value['solver']['solverCommit']
        raw = source(commit, 'contracts/pqb-ranked-v2.json')
        ranges = source(commit, 'worker/pqb/pqb_ranges.py')
        contract = json.loads(raw)
        changed = copy.deepcopy(contract)
        changed['cases'][0]['range']['count'] += 1
        with self.assertRaisesRegex(ValueError, 'vector mismatch'):
            contract_hash(json.dumps(changed).encode(), ranges)
        changed = copy.deepcopy(contract)
        changed['invalid'][-2]['attempt'] = 1
        with self.assertRaisesRegex(ValueError, 'invalid vector accepted'):
            contract_hash(json.dumps(changed).encode(), ranges)

    def altered(self, name, change, update_manifest=True):
        with tempfile.TemporaryDirectory() as temp:
            evidence = Path(temp) / 'evidence'
            shutil.copytree(EVIDENCE, evidence)
            path = evidence / name
            data = json.loads(path.read_bytes())
            change(data)
            path.write_text(json.dumps(data))
            if update_manifest:
                manifest_path = evidence / 'manifest.json'
                manifest = json.loads(manifest_path.read_bytes())
                row = next(row for row in manifest['files'] if row['path'] == name)
                row.update(bytes=path.stat().st_size, sha256=sha(path.read_bytes()))
                manifest_path.write_text(json.dumps(manifest))
            return prepare(evidence, REVIEW)

    def test_corrupt_evidence_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Evidence hash mismatch'):
            self.altered('private-image.json', lambda p: p.update(status='published'), False)

    def test_cross_bound_image_and_receipt_mismatches_are_rejected(self):
        cases = [
            ('private-image.json', lambda p: p.update(manifest=p['manifest']+'\n')),
            ('publisher/public/build-receipt.json', lambda p: p.update(binarySha256='0'*64)),
            ('publisher/public/build-receipt.json', lambda p: p.update(sourceLockSha256='0'*64)),
            ('publisher/public/build-receipt.json', lambda p: p.update(flags=['-O3','-arch=sm_89'])),
            ('publisher/public/binding.json', lambda p: p.update(solverCommit=REVIEW)),
            ('publisher/public/image.json', lambda p: p[0].update(Id='sha256:'+'0'*64)),
            ('publisher/public/image.json', lambda p: p[0]['Config'].update(Cmd=['python3','handler.py'])),
        ]
        for name, change in cases:
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.altered(name, change)


if __name__ == '__main__':
    unittest.main()
