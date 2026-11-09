import importlib.util
import pathlib
import tempfile
import unittest
from unittest.mock import patch
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('sha_pair',ROOT/'experiments/sha-rotate-add/run_pair.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class PairTests(unittest.TestCase):
 def result(self):
  rows=[]
  for name in sorted(m.NAMES):
   for sample in range(m.PAIRS):
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

 def test_unfrozen_prerequisites_refuse(self):
  self.assertTrue(all(v is None for v in m.PREREQUISITES.values()))
  with tempfile.TemporaryDirectory() as d:
   with self.assertRaisesRegex(ValueError,'not frozen'):m.check_prerequisites(pathlib.Path(d))

 def test_frozen_prerequisites_accept_and_tampering_rejects(self):
  import hashlib,json
  trace=json.dumps(dict(status='passed',candidateSha256=m.SUB,candidates=3116,hashes=6232)).encode()
  ranges=json.dumps(dict(status='completed')).encode()
  frozen={'native-trace-cpu.json':hashlib.sha256(trace).hexdigest(),'native-ranges.json':hashlib.sha256(ranges).hexdigest()}
  with tempfile.TemporaryDirectory() as d,patch.object(m,'PREREQUISITES',frozen):
   bundle=pathlib.Path(d)
   (bundle/'native-trace-cpu.json').write_bytes(trace);(bundle/'native-ranges.json').write_bytes(ranges);(bundle/'regression.json').write_bytes(ranges)
   self.assertEqual(m.check_prerequisites(bundle),frozen)
   for name in [*frozen,'regression.json']:
    with self.subTest(name=name):
     original=(bundle/name).read_bytes();(bundle/name).write_bytes(original+b' ')
     with self.assertRaises(ValueError):m.check_prerequisites(bundle)
     (bundle/name).write_bytes(original)
   wrong=json.dumps(dict(status='passed',candidateSha256='0'*64,candidates=3116,hashes=6232)).encode()
   (bundle/'native-trace-cpu.json').write_bytes(wrong)
   with patch.object(m,'PREREQUISITES',{**frozen,'native-trace-cpu.json':hashlib.sha256(wrong).hexdigest()}):
    with self.assertRaisesRegex(ValueError,'native trace prerequisite failed'):m.check_prerequisites(bundle)

 def test_four_pairs_alternate_order(self):
  rows=self.result()['samples'];first=[r['binary'] for r in rows[:8]]
  self.assertEqual(first,['baseline','candidate','candidate','baseline','baseline','candidate','candidate','baseline'])
  self.assertEqual(len(rows),32)

 def test_decision_rule_is_fixed(self):
  def summary(r1,r2):return {'taproot-round1':{'throughputGainPercent':r1[0]},'wpkh-round1':{'throughputGainPercent':r1[1]},'taproot-round2':{'throughputGainPercent':r2[0]},'wpkh-round2':{'throughputGainPercent':r2[1]}}
  self.assertEqual(m.decide(summary((2.0,5.0),(-0.5,0.0)))['outcome'],'worth-release-candidate-review')
  for r1,r2 in [((1.99,5.0),(0,0)),((5.0,5.0),(-0.51,3.0)),((-1.0,-1.0),(0,0))]:
   self.assertEqual(m.decide(summary(r1,r2))['outcome'],'no-demonstrated-benefit')
  with self.assertRaises(ValueError):m.decide({'taproot-round1':{'throughputGainPercent':9}})
