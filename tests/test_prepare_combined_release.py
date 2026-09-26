import base64
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from prepare_combined_release import prepare


class PreparationTests(unittest.TestCase):
    def test_failed_attestation_prevents_container_execution_and_proposal(self):
        calls = []
        def fail(args, **kwargs):
            calls.append(args)
            raise subprocess.CalledProcessError(1, args)
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)/'proposal'
            with self.assertRaises(subprocess.CalledProcessError):
                prepare('sha256:'+'a'*64, 'b'*40, 'candidate-test', out, fail)
            self.assertEqual(len(calls), 1)
            self.assertEqual(calls[0][:3], ['gh', 'attestation', 'verify'])
            self.assertIn('--source-digest', calls[0])
            self.assertIn('--cert-identity', calls[0])
            self.assertFalse((out/'descriptor-proposal.json').exists())

    def test_mutable_identity_rejected_before_external_call(self):
        def forbidden(*args, **kwargs): self.fail('external operation started')
        with tempfile.TemporaryDirectory() as tmp:
            for digest, commit, tag in [('latest','b'*40,'candidate-test'),
                                        ('sha256:'+'a'*64,'main','candidate-test'),
                                        ('sha256:'+'a'*64,'b'*40,'v1.0.0')]:
                with self.assertRaises(ValueError): prepare(digest,commit,tag,Path(tmp)/'out',forbidden)

    def test_mocked_extraction_remains_hold_and_uses_source_contract(self):
        calls=[]
        pipeline=dict(format='qsb-combined-candidate-v1',status='HOLD',solverCommit='b'*40,
                      searchVersion='ranked-v2',pinningUpstreamCommit='c'*40,subsetUpstreamCommit='d'*40,
                      subsetSourceLockSha256='e'*64,files={n:'f'*64 for n in ['pinning','subset','handler.py','historical_handler.py','search_ranges.py']})
        receipt=dict(binarySha256='f'*64,sourceLockSha256='e'*64)
        def run(args, **kwargs):
            calls.append(args)
            if args[0]=='gh': return SimpleNamespace(stdout='[]')
            if args[:2]==['docker','pull']: return SimpleNamespace(stdout='')
            if args[:2]==['docker','rm']: return SimpleNamespace(stdout='')
            if args[0]=='git': return SimpleNamespace(stdout=b'{"searchVersion":"ranked-v2","cases":[]}')
            return SimpleNamespace(stdout=json.dumps({n:base64.b64encode(json.dumps(v).encode()).decode() for n,v in [('pipeline.json',pipeline),('optimized-build-receipt.json',receipt)]}))
        with tempfile.TemporaryDirectory() as tmp:
            result=prepare('sha256:'+'a'*64,'b'*40,'candidate-test',Path(tmp)/'out',run)
            self.assertEqual(result['status'],'HOLD')
            self.assertEqual(result['solver']['kernelCommit'],'b'*40)
            command=calls[2]
            for flag in ['--read-only','--cap-drop','--security-opt']: self.assertIn(flag,command)
            self.assertEqual(command[command.index('--network')+1],'none')
            self.assertEqual(calls[-1][-1], 'b'*40+':contracts/ranked-v2.json')

    def test_extraction_timeout_forces_named_container_cleanup(self):
        calls=[]
        def run(args, **kwargs):
            calls.append(args)
            if args[:2]==['docker','run']:
                raise subprocess.TimeoutExpired(args, 90)
            return SimpleNamespace(stdout='[]')
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(subprocess.TimeoutExpired):
                prepare('sha256:'+'a'*64,'b'*40,'candidate-test',Path(tmp)/'out',run)
            started=calls[-2]
            self.assertEqual(calls[-1],['docker','rm','--force',started[started.index('--name')+1]])
