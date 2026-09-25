import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('memory_audit', Path(__file__).resolve().parents[1] / 'worker/promotion/validation/run_memory_audit.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class MemoryAuditTests(unittest.TestCase):
    def test_requires_sanitizer_summary_and_expected_exit(self):
        good = '========= ERROR SUMMARY: 0 errors\n'
        m.validate_result(0, 0, good)
        m.validate_result(2, 2, good)
        for code, text in [(0, ''), (99, good), (0, '========= ERROR SUMMARY: 1 error\n'),
                           (0, good + '========= ERROR SUMMARY: 2 errors\n')]:
            with self.assertRaises(ValueError):
                m.validate_result(code, 0, text)
