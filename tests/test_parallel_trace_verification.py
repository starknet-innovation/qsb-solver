"""Scheduling tests; cryptographic equivalence needs the retained native trace."""
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'experiments/generic-sha-vector'))
from verify_trace import ordered_map, load_public


class ParallelTraceTests(unittest.TestCase):
    def test_ordered_serial_parallel_equivalence(self):
        values = ['19', '0', '-7', '104', '3']
        expected = [19, 0, -7, 104, 3]
        for workers in (1, 2, 4):
            self.assertEqual(ordered_map(int, values, workers), expected)

    def test_failure_is_not_a_partial_success(self):
        for workers in (1, 2):
            with self.assertRaises(ValueError):
                ordered_map(int, ['1', 'invalid', '3'], workers)

    def test_resource_limit_rejects_invalid_counts(self):
        for workers in (0, -1, 5):
            with self.assertRaises(ValueError):
                ordered_map(int, ['1'], workers)

    def test_wrong_native_binding_never_writes_receipt(self):
        script = Path(__file__).resolve().parents[1] / 'experiments/generic-sha-vector/verify_trace.py'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result = root / 'native.json'
            result.write_text('{"status":"passed"}')
            output = root / 'receipt.json'
            run = subprocess.run([sys.executable, str(script), str(result),
                                  str(root), str(root), str(output), '--workers', '2'],
                                 capture_output=True, text=True, timeout=10)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn('wrong native result binding or state', run.stderr)
            self.assertFalse(output.exists())

    def test_missing_reference_rejected_before_pool(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                load_public(Path(directory), Path(directory))
