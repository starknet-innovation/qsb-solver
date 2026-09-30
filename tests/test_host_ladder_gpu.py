import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'experiments/host-ladder-batch'
spec=importlib.util.spec_from_file_location('host_ladder_gpu_prepare',HERE/'prepare_gpu.py')
PREP=importlib.util.module_from_spec(spec);spec.loader.exec_module(PREP)
class HostLadderGPUPreparation(unittest.TestCase):
    def test_single_frozen_kernel_and_minimal_public_scope(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)/'out';manifest=PREP.prepare(out)
            source=(out/'table-gate.cu').read_text();kernel=(out/'original-kernel.cu.inc').read_bytes()
            original=(ROOT/PREP.TREE).read_text()
            expected=PREP.extract(original,'__global__ void kernel_build_gtable(','/* ============================================================\n * Host code').encode()
            self.assertEqual(kernel,expected)
            self.assertEqual(manifest['original_kernel_sha256'],PREP.sha(expected))
            self.assertEqual(source.count('__global__ void kernel_build_gtable('),1)
            self.assertEqual(source.count('kernel_build_gtable<<<'),1)
            self.assertNotIn('candidate_build_gtable',source)
            self.assertNotIn('compute_gtable(',source)
            self.assertNotIn('kernel_search',source)
            self.assertFalse(manifest['kernel_changed'])
            for name,digest in manifest['outputs'].items():self.assertEqual(PREP.sha((out/name).read_bytes()),digest)
            with self.assertRaises(FileExistsError):PREP.prepare(out)
    def test_changed_candidate_rejected_before_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            here=Path(tmp)/'sources';here.mkdir();(here/'candidate.cpp.inc').write_text('changed')
            with self.assertRaisesRegex(ValueError,'candidate changed'):PREP.prepare(Path(tmp)/'out',here=here)
            self.assertFalse((Path(tmp)/'out').exists())
    def test_changed_baseline_rejected_before_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'root'
            for name in PREP.INPUTS:
                p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'baseline source changed'):PREP.prepare(Path(tmp)/'out',root=root)
            self.assertFalse((Path(tmp)/'out').exists())
    def test_ambiguous_extraction_rejected(self):
        with self.assertRaises(ValueError):PREP.extract('a a b','a','b')
