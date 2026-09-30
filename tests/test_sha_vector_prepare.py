import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
SCRIPT=ROOT/'experiments/generic-sha-vector/prepare.py'
spec=importlib.util.spec_from_file_location('sha_prepare',SCRIPT)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class PrepareTests(unittest.TestCase):
 def test_source_drift_refuses_output(self):
  with tempfile.TemporaryDirectory() as d:
   src=Path(d)/'source';src.write_bytes(b'changed');out=Path(d)/'out.cu'
   with patch.object(m,'SOURCE',src),patch('sys.argv',[str(SCRIPT),str(out)]):
    with self.assertRaisesRegex(ValueError,'hash mismatch'):m.main()
   self.assertFalse(out.exists())
 def test_exclusive_output_and_unchanged_source(self):
  before=m.SOURCE.read_bytes()
  with tempfile.TemporaryDirectory() as d:
   out=Path(d)/'out.cu'
   subprocess.run(['python3','-O',str(SCRIPT),str(out)],check=True,capture_output=True)
   text=out.read_text();self.assertIn('namespace baseline',text);self.assertIn('namespace candidate',text)
   self.assertIn('const uint4 first',text);self.assertIn('reference(ref,w.data()+k*64)',text)
   saved=out.read_bytes()
   result=subprocess.run(['python3',str(SCRIPT),str(out)],capture_output=True)
   self.assertNotEqual(result.returncode,0);self.assertEqual(out.read_bytes(),saved)
  self.assertEqual(m.SOURCE.read_bytes(),before)
