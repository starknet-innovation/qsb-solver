import base64
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'worker/promotion/validation'))
import fresh_subset_search as s

PIN={'sequence':0x80000000,'locktime':500000000}
PUB={'request':{'action':'export','scriptVersion':s.common.VERSION,'stage':'pinning'}}
EXPORTED={'scriptVersion':s.common.VERSION,'parameterBase64':base64.b64encode(b'public').decode(),'parameterSha256':hashlib.sha256(b'public').hexdigest()}

def reference(event):
    if event['action']=='export':return EXPORTED
    if event['stage']=='pinning':return {'scriptVersion':s.common.VERSION,'valid':True,**PIN}
    return {'scriptVersion':s.common.VERSION,'valid':True,'indices':list(range(141,150))}

class SubsetTests(unittest.TestCase):
    def test_stage_advancement_verifies_prior_solutions(self):
        calls=[]
        def verify(event):calls.append(event);return reference(event)
        event,exported,raw=s.export_stage(PUB,PIN,'round1',verify)
        self.assertEqual([e['stage'] for e in calls],['pinning','round1']);self.assertEqual(raw,b'public')
        calls.clear()
        s.export_stage(PUB,{**PIN,'round1':list(range(141,150))},'round2',verify)
        self.assertEqual([e['stage'] for e in calls],['pinning','round1','round2'])
        self.assertEqual(calls[1]['candidates'],['indices=0,1,2,3,4,5,6,7,8'])

    def test_wrong_pin_prior_round_and_version_reject(self):
        for stage,solution in [('round1',PIN),('round2',{**PIN,'round1':list(range(141,150))})]:
            with self.assertRaises(ValueError):s.export_stage(PUB,solution,stage,lambda e:{'valid':False})
        with self.assertRaises(ValueError):s.export_stage(PUB,{**PIN,'round1':[1]*9},'round2',reference)
        with self.assertRaises(ValueError):s.export_stage(PUB,{**PIN,'round1':list(range(9))},'round2',reference)
        with self.assertRaises(ValueError):s.export_stage(PUB,{**PIN,'secret':'no'},'round1',reference)

    def test_all_candidates_verified_and_indices_converted(self):
        event=s.stage_event(PUB,PIN,'round1');unit=s.work_range('round1',0)
        record='indices=0,1,2,3,4,5,6,7,8\n'
        calls=[]
        def verify(e):calls.append(e);return reference(e)
        solution=s.checked_solution(event,PIN,[record,record],unit,verify)
        self.assertEqual(solution,{**PIN,'round1':list(range(141,150))});self.assertEqual(len(calls),2)
        with self.assertRaises(ValueError):s.checked_solution(event,PIN,[record],unit,lambda e:{'valid':False})
        with self.assertRaises(ValueError):s.checked_solution(event,PIN,[record],s.work_range('round1',1),reference)

    def test_uncertain_intent_and_tampered_result_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);d=root/'range-00000000';d.mkdir()
            record={'attempt':0,'status':'compute-intent','binding':'b','workRange':s.work_range('round1',0)}
            s.common.save(d/'record.json',record)
            with self.assertRaisesRegex(ValueError,'Uncertain'):s.resume(root,'b','round1')
            (d/'compute.log').write_text('Done enum:')
            s.common.save(d/'result.json',{'logSha256':s.common.sha(d/'compute.log')})
            record.update(status='complete',resultSha256=s.common.sha(d/'result.json'));s.common.save(d/'record.json',record)
            self.assertEqual(s.resume(root,'b','round1'),(1,None))
            (d/'compute.log').write_text('changed')
            with self.assertRaisesRegex(ValueError,'Log changed'):s.resume(root,'b','round1')

    def test_durable_one_shot_and_ack_precedes_compute(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name,value in [('public',PUB),('solution',PIN),('hashes',{})]:(root/(name+'.json')).write_text(json.dumps(value))
            args=SimpleNamespace(output=root/'stage',public=root/'public.json',solution=root/'solution.json',reference_hashes=root/'hashes.json',
                binary=root/'bin',binary_sha256='a'*64,reference=root/'reference',stage='round1',deadline=int(time.time())+3600,
                range_timeout=1,mode='prepare',attempt=None,intent_ack_dir=root/'acks')
            order=[]
            def ack(path,*rest):
                self.assertEqual(json.loads(path.read_text())['status'],'compute-intent');order.append('ack')
            def compute(binary,raw,unit,directory,timeout,prior):
                order.append('compute');(directory/'compute.log').write_text('Done enum:')
                return {'candidates':[],'logSha256':s.common.sha(directory/'compute.log')}
            with patch.object(s.common,'verify_artifacts'),patch.object(s.common,'verify_public'),patch.object(s.common,'cpu',side_effect=lambda r,e:reference(e)),patch.object(s.subprocess,'check_output',return_value='GPU-one'),patch.object(s.common,'await_intent_ack',side_effect=ack),patch.object(s,'compute',side_effect=compute):
                self.assertEqual(s.run(args)['status'],'prepared');self.assertEqual(order,[])
                args.mode='execute';args.attempt=0
                self.assertEqual(s.run(args)['status'],'complete');self.assertEqual(order,['ack','compute'])
                with self.assertRaisesRegex(ValueError,'unexecuted'):s.run(args)
                args.mode='prepare';self.assertEqual(s.run(args)['attempt'],1)

    def test_actual_nonzero_process_never_credits(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);binary=root/'fake';binary.write_text('#!/bin/sh\necho incomplete\nexit 2\n');binary.chmod(0o700)
            with self.assertRaisesRegex(ValueError,'failed'):s.compute(binary,b'public',s.work_range('round1',0),root,1,PIN)
            self.assertIn('incomplete',(root/'compute.log').read_text())

if __name__=='__main__':unittest.main()
