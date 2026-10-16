import base64
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'worker/promotion/validation'))
import run_corrected_pinning_trace as c


def plan():
    return dict(scriptVersion=c.VERSION,status='PREPARED_NOT_EXECUTED',parameterBase64=base64.b64encode(b'public').decode(),
                parameterSha256=hashlib.sha256(b'public').hexdigest(),expectedHashes=80,
                cases=[dict(sequence=s,locktime=t,sequenceCount=1,locktimeCount=4,
                    expected={f'{s}:{v}:{r}':'a'*64 for v in range(t,t+4) for r in (0,1)}) for s,t in c.EXPECTED_CASES])


class CollectorTests(unittest.TestCase):
    def test_exact_bounded_inventory(self):
        self.assertEqual(c.validate_plan(plan())['expectedHashes'],80)

    def test_inventory_and_parameter_mutations_fail(self):
        for field,value in [('scriptVersion','legacy'),('expectedHashes',79),('parameterSha256','b'*64),('status','RUNNING')]:
            p=plan();p[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):c.validate_plan(p)
        for mutate in [lambda p:p['cases'].pop(),lambda p:p['cases'].append(p['cases'][0]),
                       lambda p:p['cases'][0].update(locktimeCount=100),lambda p:p['cases'][0]['expected'].pop(next(iter(p['cases'][0]['expected'])))]:
            p=plan();mutate(p)
            with self.assertRaises(ValueError):c.validate_plan(p)

    def test_collector_preserves_failure_and_refuses_reexecution(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);p=root/'plan.json';p.write_text(json.dumps(plan()));out=root/'result.json'
            with patch.object(c,'validate_receipt',return_value={}), patch.object(c.subprocess,'check_output',return_value='NVIDIA A10G, test, 1'), patch.object(c,'execute',return_value={'exit':2,'hits':{},'log':'native failure'}):
                with self.assertRaises(ValueError):c.run(p,c.sha(p),root/'receipt.json','unused',root/'normal',out,10**12)
                saved=json.loads(out.read_text())
                self.assertEqual(saved['status'],'FAILED')
                self.assertEqual(saved['ranges'][0]['trace']['exit'],2)
                with self.assertRaises(FileExistsError):c.run(p,c.sha(p),root/'receipt.json','unused',root/'normal',out,10**12)

    def test_receipt_checks_flags_and_exact_normal_binary(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name in ['pinning','pinning-trace','trace.diff']:(root/name).write_bytes(name.encode())
            digest=c.sha(root/'pinning')
            r=dict(architecture='sm_86',flags=['-O3','-arch=sm_86','-DQSB_SLOTPIPE=0'],
                   files={n:c.sha(root/n) for n in ['pinning','pinning-trace','trace.diff']})
            path=root/'receipt.json';path.write_text(json.dumps(r))
            with patch.object(c,'NORMAL_SHA256',digest):
                c.validate_receipt(path,c.sha(path),root/'pinning')
                r['flags'].append('-DEASY=1');path.write_text(json.dumps(r))
                with self.assertRaises(ValueError):c.validate_receipt(path,c.sha(path),root/'pinning')


if __name__=='__main__':unittest.main()
