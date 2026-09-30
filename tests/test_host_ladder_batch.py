import importlib.util
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location('host_ladder_prepare',ROOT/'experiments/host-ladder-batch/prepare.py')
PREP=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(PREP)
class HostLadderPreparation(unittest.TestCase):
    def test_frozen_minimal_extraction(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)/'out';m=PREP.prepare(out);s=(out/'ladder.cpp').read_text()
            self.assertIn('static void gt_build_ladders',s)
            self.assertIn('EC_POINTs_make_affine',s)
            self.assertNotIn('__global__',s)
            self.assertNotIn('gt_spot_check',s)
            self.assertNotIn('fopen(argv[1],"rb")',s)
            for name,digest in m['outputs'].items():self.assertEqual(PREP.sha((out/name).read_bytes()),digest)
            with self.assertRaises(FileExistsError):PREP.prepare(out)
    def test_frozen_mismatch_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name in PREP.INPUTS:
                p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'wrong')
            with self.assertRaises(ValueError):PREP.prepare(root/'out',root)
            self.assertFalse((root/'out').exists())
    def test_ambiguous_extraction_rejected(self):
        with self.assertRaises(ValueError):PREP.between('a a b','a','b')

class HostLadderTimeoutEvidence(unittest.TestCase):
    def test_timeout_preserves_bytes_and_has_no_success_receipt(self):
        from unittest.mock import patch
        import subprocess
        import json
        spec=importlib.util.spec_from_file_location('host_ladder_check',ROOT/'experiments/host-ladder-batch/check.py')
        check=importlib.util.module_from_spec(spec);spec.loader.exec_module(check)
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/'out'
            error=subprocess.TimeoutExpired(['fixed-public-gate'],120,output=b'partial output',stderr=b'partial error')
            with patch.object(check.subprocess,'run',side_effect=error):
                with self.assertRaisesRegex(ValueError,'timed out'):check.check(Path(tmp)/'binary',output)
            self.assertEqual((output/'normal.stdout').read_text(),'partial output')
            self.assertEqual((output/'normal.stderr').read_text(),'partial error')
            self.assertEqual(json.loads((output/'failure.json').read_text())['reason'],'timeout')
            self.assertFalse((output/'checks.json').exists())
