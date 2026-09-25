import importlib.util
from pathlib import Path
import tempfile
import time
import unittest

spec = importlib.util.spec_from_file_location('benchmark', Path(__file__).parents[1] / 'worker/promotion/validation/benchmark.py')
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)

class BenchmarkTests(unittest.TestCase):
    def test_identity_rejects_wrong_binary(self):
        with tempfile.NamedTemporaryFile() as f:
            f.write(b'wrong'); f.flush()
            with self.assertRaises(ValueError):
                b.checked_hash(f.name, b.CANDIDATE_SHA)

    def test_deadline_prevents_launch(self):
        with self.assertRaises(TimeoutError):
            b.execute('/not-executable', {}, 1, 0, time.monotonic() - 1)

    def test_nonzero_cannot_claim_completion(self):
        with tempfile.TemporaryDirectory() as tmp:
            executable = Path(tmp) / 'fake'
            executable.write_text('#!/bin/sh\necho Done:\nexit 2\n')
            executable.chmod(0o700)
            with self.assertRaises(RuntimeError):
                b.execute(executable, dict(params='', sequence=0, locktime=0), 1, 0, time.monotonic()+10)
