import copy
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from combined_descriptor import proposal
from release_descriptor import descriptor


class CombinedDescriptorTests(unittest.TestCase):
    def setUp(self):
        self.pipeline = dict(format='qsb-combined-candidate-v1', status='HOLD',
                             solverCommit='a'*40, searchVersion='ranked-v2',
                             pinningUpstreamCommit='b'*40, subsetUpstreamCommit='c'*40,
                             subsetSourceLockSha256='d'*64,
                             files={n: 'e'*64 for n in ['pinning', 'subset', 'handler.py', 'historical_handler.py', 'search_ranges.py']})
        self.receipt = dict(binarySha256='e'*64, sourceLockSha256='d'*64)
        self.contract = b'{"searchVersion":"ranked-v2","cases":[]}'

    def build(self, pipeline=None, receipt=None, commit='a'*40, digest='sha256:'+'f'*64):
        return proposal(json.dumps(self.pipeline if pipeline is None else pipeline).encode(),
                        json.dumps(self.receipt if receipt is None else receipt).encode(), commit, digest, self.contract)

    def test_combined_wire_identity_and_historical_compatibility(self):
        result = self.build()
        self.assertEqual(result['solver']['kernelCommit'], 'a'*40)
        self.assertEqual(result['status'], 'HOLD')
        self.assertNotIn('fresh-final-image-wallet-proof', result['remainingApproval'])
        self.assertIn('native-sm86-correctness-and-matched-a10g-performance', result['remainingApproval'])
        self.assertEqual(result['solver']['schemaVersion'], 3)
        self.assertRegex(result['solver']['searchContract'], '^[0-9a-f]{64}$')
        self.assertNotEqual(descriptor('a'*40, 'sha256:'+'f'*64)['kernelCommit'], 'a'*40)
        self.assertNotIn('binding', result['solver'])  # consumer schema remains strict v3

    def test_mismatched_or_mutable_identities_fail(self):
        for field, value in [('solverCommit', 'b'*40), ('status', 'READY'),
                             ('searchVersion', 'ranked-v1'), ('subsetSourceLockSha256', 'main')]:
            p = copy.deepcopy(self.pipeline); p[field] = value
            with self.assertRaises(ValueError): self.build(pipeline=p)
        for field in ['binarySha256', 'sourceLockSha256']:
            r = dict(self.receipt); r[field] = '0'*64
            with self.assertRaises(ValueError): self.build(receipt=r)
        for digest in ['latest', 'sha256:'+'F'*64]:
            with self.assertRaises(ValueError): self.build(digest=digest)

    def test_missing_or_extra_bound_artifacts_rejected(self):
        for action in ['missing', 'extra', 'invalid']:
            p = copy.deepcopy(self.pipeline)
            if action == 'missing': del p['files']['subset']
            elif action == 'extra': p['files']['unexpected'] = 'e'*64
            else: p['files']['pinning'] = 'latest'
            with self.assertRaises(ValueError): self.build(pipeline=p)

    def test_evidence_hashes_bind_exact_bytes(self):
        p = json.dumps(self.pipeline).encode(); r = json.dumps(self.receipt).encode()
        left = proposal(p, r, 'a'*40, 'sha256:'+'f'*64, self.contract)
        right = proposal(p+b'\n', r, 'a'*40, 'sha256:'+'f'*64, self.contract)
        self.assertEqual(left['solver'], right['solver'])
        self.assertNotEqual(left['binding']['pipelineSha256'], right['binding']['pipelineSha256'])


    def test_architecture_binding(self):
        for arch in ('sm_86','sm_89'):
            p=dict(self.pipeline,architecture=arch)
            r=dict(self.receipt,architecture=arch,flags=['-O3','-arch='+arch])
            self.assertEqual(self.build(pipeline=p,receipt=r)['status'],'HOLD')
            for broken in (dict(r,architecture='sm_80'),dict(r,flags=[]),dict(r,flags=['-arch='+arch]*2)):
                with self.assertRaises(ValueError):self.build(pipeline=p,receipt=broken)
