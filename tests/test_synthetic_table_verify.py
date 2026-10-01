import copy
import hashlib
import importlib.util
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch
from test_synthetic_table_results import m,receipt
spec=importlib.util.spec_from_file_location('synthetic_verify',Path(__file__).resolve().parents[1]/'experiments/synthetic-table-e2e/verify.py')
v=importlib.util.module_from_spec(spec)
with patch.dict(sys.modules,{'run':m}):spec.loader.exec_module(v)
BINARY='a'*64
IMAGE='ghcr.io/starknet-innovation/qsb-solver@sha256:'+'b'*64

def envelope():
    r=receipt();r.update(binarySha256=BINARY,noSolverSearch=True,solverThroughputMeasured=False,measurementScope=m.SCOPE)
    files={'exit-code.txt':'0','binary.sha256':BINARY+'  table-gate','runtime.txt':IMAGE,'gpu.txt':'NVIDIA A10G, GPU-example, 570.1'}
    for row in r['sanitizers']:
        stem=row['tool']+'-'+row['arm']
        summary='========= RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)' if row['tool']=='racecheck' else '========= ERROR SUMMARY: 0 errors'
        log='COMPUTE-SANITIZER\n'+m.COMPLETE+'\n'+summary+'\n'
        row['logSha256']=hashlib.sha256(log.encode()).hexdigest()
        files[stem+'.log']=log;files[stem+'.json']=json.dumps(row['report'])
    for row in r['samples']:
        stem=f"sample-{row['repetitions']}-{row['pair']}-{row['arm']}"
        files[stem+'.log']=m.COMPLETE+'\n';files[stem+'.json']=json.dumps(row['report'])
    r['summary']=m.summarize(r);files['result.json']=json.dumps(r)
    return files

class OfflineVerification(unittest.TestCase):
    def test_complete_bound_envelope(self):
        self.assertEqual(v.validate(envelope(),BINARY,IMAGE,0)['status'],'passed')
    def test_identity_terminal_and_log_tampering(self):
        for key,value in [('runtime.txt','image:latest'),('binary.sha256','b'*64+' table-gate'),('gpu.txt','NVIDIA A10G'),('exit-code.txt','1'),('memcheck-baseline.log','truncated'),('sample-1-0-baseline.log','')]:
            files=envelope();files[key]=value
            with self.assertRaises(ValueError):v.validate(files,BINARY,IMAGE,0)
        with self.assertRaises(ValueError):v.validate(envelope(),BINARY,IMAGE,1)
    def test_child_report_must_match_journal(self):
        files=envelope();r=json.loads(files['sample-1-0-baseline.json']);r['arm']='candidate';files['sample-1-0-baseline.json']=json.dumps(r)
        with self.assertRaises(ValueError):v.validate(files,BINARY,IMAGE,0)
