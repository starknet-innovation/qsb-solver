import importlib.util
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'worker/promotion/validation'))
import run_a10g as gate

class A10GBinding(unittest.TestCase):
    def test_only_exact_candidate_is_accepted(self):
        good=dict(solverCommit=gate.COMMIT,architecture='sm_86',files=dict(pinning=gate.PIN,subset=gate.SUB))
        gate.validate_binding(good)
        for change in (dict(solverCommit='0'*40),dict(architecture='sm_89'),dict(files=dict(pinning=gate.PIN,subset='0'*64))):
            with self.assertRaises(ValueError):gate.validate_binding(dict(good,**change))
