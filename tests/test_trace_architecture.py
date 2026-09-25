import copy
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('trace_build', Path(__file__).resolve().parents[1]/'worker/promotion/validation/build_trace.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

class TraceArchitectureTests(unittest.TestCase):
    def test_matching_architectures(self):
        lock = {'flags': ['-O3', '-arch=sm_89', '-DREAL_PREDICATE=1']}
        for architecture in ['sm_86', 'sm_89']:
            build = {'architecture': architecture, 'flags': ['-O3', '-arch='+architecture, '-DREAL_PREDICATE=1'], 'sourceLockSha256': 'source'}
            self.assertEqual(mod.checked_flags(lock, build, 'source'), build['flags'])
            for key,value in [('architecture','sm_90'),('sourceLockSha256','other'),('flags',['-O3','-arch=sm_89','-DREAL_PREDICATE=0'])]:
                bad = copy.deepcopy(build); bad[key] = value
                with self.assertRaises(ValueError): mod.checked_flags(lock,bad,'source')

    def test_duplicate_or_missing_locked_architecture(self):
        for flags in [[], ['-arch=sm_89','-arch=sm_89']]:
            with self.assertRaises(ValueError): mod.checked_flags({'flags':flags},{'architecture':'sm_86'},'source')
