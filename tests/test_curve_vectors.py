import importlib.util
from pathlib import Path
import struct
import unittest

spec = importlib.util.spec_from_file_location('vectors', Path(__file__).parents[1] / 'worker/promotion/validation/curve_vectors.py')
vectors = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vectors)

class CurveVectors(unittest.TestCase):
    def test_edges_and_layout(self):
        values = vectors.scalars()
        for edge in [0, 1, vectors.N-1, vectors.N, vectors.N+1, vectors.MASK]:
            self.assertIn(edge, values)
        self.assertEqual(len(values), len(set(values)))
        raw = vectors.encode(values)
        self.assertEqual(struct.unpack('<I',raw[:4])[0], len(values))
        self.assertEqual(len(raw), 4 + 144*len(values))
        self.assertEqual([int.from_bytes(raw[4+144*i:36+144*i], 'little') for i in range(len(values))], values)

class AuditVerdict(unittest.TestCase):
    def test_partial_or_error_cannot_pass(self):
        spec = importlib.util.spec_from_file_location('runner', Path(vectors.__file__).with_name('run_curve.py'))
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        good = 'Point GPU audit PASS: chunks=15 input_cases=10 point_cases=20 infinity_cases=4 table_checks=504 errors=0'
        self.assertEqual(runner.validate_output(good,10)['pointCases'],20)
        for bad in [good.replace('errors=0','errors=1'),good.replace('point_cases=20','point_cases=18'),good+good,'']:
            with self.assertRaises(ValueError):
                runner.validate_output(bad,10)
