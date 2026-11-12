import copy
import gzip
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import check_pqb_final as final
import verify_pqb_build as build
from pqb_descriptor import sha


class FinalReviewTests(unittest.TestCase):
    def test_archive_requires_original_hash_and_unambiguous_safe_inventory(self):
        raw=gzip.compress(b'{}')
        with self.assertRaisesRegex(ValueError,'archive hash mismatch'):
            final.native_rows(raw,'0'*64,{}, {})
        for payload in (b'{"x":"one","x":"two"}',b'{"../outside":"bad"}',b'{"/absolute":"bad"}'):
            raw=gzip.compress(payload)
            with self.assertRaises(ValueError):final.native_rows(raw,sha(raw),{}, {})

    def test_failed_or_partial_host_receipt_cannot_be_credited(self):
        raw=gzip.compress(b'{"exit-code.txt":"1","stage.txt":"all",'
                          b'"runtime-identity-check.json":"{\\"status\\":\\"failed\\"}"}')
        with self.assertRaisesRegex(ValueError,'runtime identity differs'):
            final.native_rows(raw,sha(raw),{}, {})

    def test_verified_policy_binds_source_workflow_runner_and_run(self):
        commit='a'*40;ref='refs/heads/codex/pqb-qualify-test'
        cert={'sourceRepositoryURI':'https://github.com/starknet-innovation/qsb-solver',
              'sourceRepositoryDigest':commit,'sourceRepositoryRef':ref,
              'buildSignerURI':'https://github.com/'+build.WORKFLOW+'@'+ref,
              'buildSignerDigest':commit,'runnerEnvironment':'github-hosted',
              'runInvocationURI':'https://github.com/starknet-innovation/qsb-solver/actions/runs/123/attempts/1'}
        entry={'verificationResult':{'signature':{'certificate':cert}}}
        build.verify_policy([entry],commit,ref,123)
        for key,value in [('sourceRepositoryDigest','b'*40),('sourceRepositoryRef',ref+'wrong'),
                          ('buildSignerURI','https://github.com/attacker/build'),
                          ('runnerEnvironment','self-hosted'),('runInvocationURI',cert['runInvocationURI'].replace('/123/','/1234/'))]:
            changed=copy.deepcopy(entry);changed['verificationResult']['signature']['certificate'][key]=value
            with self.assertRaises(ValueError):build.verify_policy([changed],commit,ref,123)
        with self.assertRaises(ValueError):build.verify_policy([],commit,ref,123)
