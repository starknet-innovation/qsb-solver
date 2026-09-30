import importlib.util
import pathlib
import tempfile
import unittest
from unittest.mock import patch
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('sha_pair',ROOT/'experiments/generic-sha-vector/run_pair.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class PairTests(unittest.TestCase):
 def result(self):
  rows=[]
  for name in sorted(m.NAMES):
   for sample in range(3):
    for binary in (('baseline','candidate') if sample%2==0 else ('candidate','baseline')):
     rows.append(dict(name=name,sample=sample,binary=binary,count=m.COUNT,rank=0,seconds=10,exit=0,timedOut=False,log='[GPU 0] Done enum:',summary=f'STATUS=EXHAUSTED 1 total_attempts={m.COUNT} elapsed_s=10 hits=0',hitFiles={}))
  return dict(baselineSha256=m.BASELINE,candidateSha256=m.SUB,samples=rows)
 def test_complete_interleaved_pair(self):
  result=m.summarize(self.result());self.assertEqual(set(result),m.NAMES)
  self.assertTrue(all(v['throughputGainPercent']==0 for v in result.values()))
 def test_partial_or_failed_cannot_claim_gain(self):
  for mode in ['missing','failure','identity','infinite','hits']:
   with self.subTest(mode=mode):
    r=self.result()
    if mode=='missing':r['samples'].pop()
    if mode=='failure':r['samples'][0]['exit']=2
    if mode=='identity':r['candidateSha256']='0'*64
    if mode=='infinite':r['samples'][0]['seconds']=float('inf')
    if mode=='hits':r['samples'][0]['hitFiles']={'hit.txt':'unverified'}
    with self.assertRaises(ValueError):m.summarize(r)
 def test_wrong_binary_fails_before_gpu_or_process(self):
  with tempfile.TemporaryDirectory() as d:
   p=pathlib.Path(d);(p/'baseline').write_bytes(b'wrong')
   with patch('sys.argv',['run_pair.py',str(p),str(p/'output.json'),'0'*64]),patch.object(m.subprocess,'check_output') as gpu,patch.object(m.subprocess,'Popen') as proc:
    with self.assertRaisesRegex(ValueError,'binary hash mismatch'):m.main()
    gpu.assert_not_called();proc.assert_not_called()
   self.assertFalse((p/'output.json').exists())
