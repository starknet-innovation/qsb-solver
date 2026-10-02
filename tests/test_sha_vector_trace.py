import pathlib
import subprocess
import sys
import tempfile
import unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/generic-sha-vector'))
from trace_source import instrument, TRACE


class TraceTests(unittest.TestCase):
    def test_only_frozen_candidate_is_instrumented(self):
        source=ROOT/'research/optimized-subset/subset/tests/gpu_epochs/tree.cu'
        original=source.read_bytes()
        with self.assertRaises(ValueError):instrument(original.decode())
        with tempfile.TemporaryDirectory() as d:
            target=pathlib.Path(d)/'subset/tests/gpu_epochs/tree.cu'
            target.parent.mkdir(parents=True);target.write_bytes(original)
            subprocess.run(['patch','--batch','-p1','-i',str(ROOT/'experiments/generic-sha-vector/generic-tail-vector.patch')],cwd=d,check=True,capture_output=True)
            candidate=target.read_text();traced=instrument(candidate)
            self.assertEqual(traced.replace(TRACE,''),candidate)
            self.assertEqual(traced.count('TRACE_SUB indices='),1)
            with self.assertRaises(ValueError):instrument(traced)
        self.assertEqual(source.read_bytes(),original)
