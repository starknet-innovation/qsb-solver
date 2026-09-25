import copy
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'worker/promotion/validation'))
from run_a10g import COMMIT,PIN,SUB
from run_a10g_trace import validate_trace

class A10gTraceTests(unittest.TestCase):
    def test_cross_build_and_inventory_rejected(self):
        binding={'solverCommit':COMMIT,'architecture':'sm_86','files':{'pinning':PIN,'subset':SUB},'subsetSourceLockSha256':'locked'}
        receipt={'architecture':'sm_86','unmodifiedBinarySha256':SUB,'sourceLockSha256':'locked','files':{'trace-subset':'a','trace.diff':'b'}}
        validate_trace(receipt,binding)
        for key,value in [('architecture','sm_89'),('unmodifiedBinarySha256','older'),('sourceLockSha256','other'),('files',{'trace-subset':'a'})]:
            changed=copy.deepcopy(receipt);changed[key]=value
            with self.assertRaises(ValueError):validate_trace(changed,binding)
        for key,value in [('solverCommit','main'),('architecture','sm_89')]:
            changed=copy.deepcopy(binding);changed[key]=value
            with self.assertRaises(ValueError):validate_trace(receipt,changed)
