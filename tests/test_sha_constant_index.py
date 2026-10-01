"""Source-bound checks for the independent four-block SHA indexing experiment."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('sha_constant_index',ROOT/'experiments/sha-constant-index/prepare.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class ConstantIndexTests(unittest.TestCase):
    def test_exact_source_and_round_mapping(self):
        original=m.SOURCE.read_text();changed=m.transform(original);body=m.function(changed)
        self.assertIn('const int stop=offset+64;',body)
        self.assertIn('for(int offset=0;offset<256;)',body)
        self.assertIn('for(;offset<stop;offset+=8)',body)
        self.assertEqual(body.count('S2Round('),8)
        self.assertEqual(body.count('output['),16)
        for n in range(8):
            self.assertEqual(body.count('schedule[offset'+(f'+{n}' if n else '')+']'),1)
        self.assertNotIn('uint4',body)
        self.assertNotIn('QSB_CONST_SCHEDULE[block]',changed)
        # The generic-tail optimization rejected in PR7 is not part of this experiment.
        start=original.index('__device__ __forceinline__ void qsb_compress_generic_tail(')
        end=original.index('\n__global__',start)
        self.assertIn(original[start:end],changed)
    def test_drift_fails_closed(self):
        with self.assertRaisesRegex(ValueError,'hash mismatch'):
            m.transform(m.SOURCE.read_text()+'\n')
if __name__=='__main__':unittest.main()
