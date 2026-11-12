import importlib.util
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from check_pqb_final import native_device_matches as checker
spec=importlib.util.spec_from_file_location('device_unit',ROOT/'research/pqb-ranked/measure/run_full_unit.py')
full=importlib.util.module_from_spec(spec);spec.loader.exec_module(full)


class NativeDeviceTests(unittest.TestCase):
    def test_reviewed_device_is_required_by_both_native_and_consumer_checkers(self):
        for check in (checker,full.native_device_matches):
            for expected in ('A10G','L4'):
                for name in (expected,'NVIDIA '+expected):
                    self.assertTrue(check([{'device':name}],expected))
                for setups in ([],[{'device':'cpu-emulation'}],[{'device':'fake '+expected}],
                               [{'device':'A10G' if expected=='L4' else 'L4'}],
                               [{'device':expected},{'device':expected}]):
                    with self.subTest(expected=expected,setups=setups):self.assertFalse(check(setups,expected))
            with self.assertRaises(ValueError):check([{'device':'anything'}],'anything')
