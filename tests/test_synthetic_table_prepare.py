import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'experiments/synthetic-table-e2e'
spec=importlib.util.spec_from_file_location('synthetic_table_prepare',HERE/'prepare.py')
PREP=importlib.util.module_from_spec(spec);spec.loader.exec_module(PREP)
class SyntheticTablePreparation(unittest.TestCase):
    def test_only_isolated_harness_changes(self):
        reuse=ROOT/'experiments/host-ladder-batch'
        spec=importlib.util.spec_from_file_location('original_table_prepare',reuse/'prepare_gpu.py')
        base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);base.prepare(root/'base');manifest=PREP.prepare(root/'candidate')
            old=(reuse/'gpu-harness.cu.inc').read_bytes();original=(root/'base/table-gate.cu').read_bytes();new=(root/'candidate/table-gate.cu').read_bytes()
            self.assertTrue(original.endswith(old));self.assertTrue(new.startswith(original[:-len(old)]))
            self.assertEqual(new.count(b'__global__ void kernel_build_gtable('),1)
            self.assertEqual(new.count(b'int main('),1)
            self.assertNotIn(b'kernel_search',new);self.assertNotIn(b'candidate_build_gtable',new)
            self.assertTrue(manifest['noSolverSearch']);self.assertEqual(manifest['repetitions'],[1,4,16]);self.assertEqual(manifest['publicScalar'],1)
            self.assertEqual((root/'base/original-kernel.cu.inc').read_bytes(),(root/'candidate/original-kernel.cu.inc').read_bytes())
            for name,digest in manifest['outputs'].items():self.assertEqual(PREP.sha((root/'candidate'/name).read_bytes()),digest)
            with self.assertRaises(FileExistsError):PREP.prepare(root/'candidate')
    def test_changed_reused_code_fails_before_import_or_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);reuse=root/'experiments/host-ladder-batch';reuse.mkdir(parents=True)
            (reuse/'prepare_gpu.py').write_text('raise RuntimeError("must not execute changed helper")')
            with self.assertRaisesRegex(ValueError,'reused extraction changed'):PREP.prepare(root/'output',root)
            self.assertFalse((root/'output').exists())
    def test_changed_old_harness_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);reuse=root/'experiments/host-ladder-batch';reuse.mkdir(parents=True)
            (reuse/'prepare_gpu.py').write_bytes((ROOT/'experiments/host-ladder-batch/prepare_gpu.py').read_bytes())
            (reuse/'gpu-harness.cu.inc').write_text('changed')
            with self.assertRaisesRegex(ValueError,'reused extraction changed'):PREP.prepare(root/'output',root)
            self.assertFalse((root/'output').exists())
