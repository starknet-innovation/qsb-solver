import base64
import gzip
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
import uuid
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ops/fresh-proof'))
import submit as m

class SubmissionTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        self.campaign=dict(campaignId=str(uuid.uuid4()),requestHash='a'*64,candidateSource=m.SOURCE,imageDigest=m.IMAGE)
        self.b=m.Budget.create(self.root/'budget.sqlite',self.campaign);self.j=m.Journal(self.b)
        self.j.initialize('b'*64,'c'*64,self.campaign['campaignId'])
        self.token=str(uuid.uuid4());self.path=self.root/'state.json';self.receipt=self.root/'command.json'
        self.request=dict(statePath=str(self.path.resolve()),controllerCommit='test',region='eu-west-1',instanceType='g5.xlarge')
        self.b.reserve(self.token,self.request,2_000_000)
        batch=dict(batchId=str(uuid.uuid4()),request=dict(stage='pinning',attempt=0,manifestHash='c'*64),maxAttempts=1)
        self.j.register(self.token,json.dumps(batch).encode(),lambda b:b['request'])
        resource=dict(instanceId='i-12345678901234567',volumeIds=['vol-test'],clientToken=self.token)
        self.b.attach(self.token,self.request,resource)
        self.state=dict(token=self.token,name='qsb-bench-'+self.token[:8],controllerCommit='test',phase='launched',instanceId=resource['instanceId'],deadline=1790400000)
        self.state['proofBudget']=m.Guard(self.b,self.token,self.path,self.campaign).binding
        self.b.bind_scope(self.token,dict(deadline=self.state['deadline'],controllerCommit='test'))
        self.path.write_text(json.dumps(self.state));self.calls=[];self.command=str(uuid.uuid4())
    def aws(self,args):
        self.calls.append(args)
        with self.b.transaction() as db:
            self.assertEqual(db.execute('SELECT state,command_text FROM proof_sessions').fetchone(),('command-intent','public command'))
        return dict(Command=dict(CommandId=self.command,InstanceIds=[self.state['instanceId']],DocumentName='AWS-RunShellScript'))
    def run_submit(self,aws=None,now=lambda:1790398800):
        return m.submit_once(self.b,self.path,self.campaign,'public command',self.receipt,aws or self.aws,now)
    def test_one_call_intent_precedes_provider_and_saved_id_blocks_repeat(self):
        result=self.run_submit();self.assertEqual(result['commandId'],self.command)
        self.assertEqual(json.loads(self.receipt.read_text())['Command']['CommandId'],self.command)
        with self.assertRaises(ValueError):self.run_submit()
        self.assertEqual(len(self.calls),1)
    def test_unknown_send_keeps_intent_and_prevents_restart(self):
        def timeout(args):self.calls.append(args);raise TimeoutError('unknown')
        with self.assertRaises(TimeoutError):self.run_submit(timeout)
        with self.assertRaises(ValueError):self.run_submit()
        self.assertEqual(len(self.calls),1);self.assertFalse(self.receipt.exists())
    def test_wrong_resource_or_frozen_deadline_rejects_before_send(self):
        for key,value in [('instanceId','i-other'),('deadline',1790500000),('token',str(uuid.uuid4()))]:
            self.path.write_text(json.dumps(dict(self.state,**{key:value})))
            with self.subTest(key=key),self.assertRaises(ValueError):self.run_submit()
        self.assertEqual(self.calls,[])
    def test_time_consumed_during_claim_never_sends(self):
        times=iter([1790398800,1790399990])
        with self.assertRaisesRegex(ValueError,'consumed'):self.run_submit(now=lambda:next(times))
        with self.assertRaises(ValueError):self.run_submit()
        self.assertEqual(self.calls,[])
    def test_mismatched_response_id_is_saved_for_reconciliation(self):
        def bad(args):return dict(Command=dict(CommandId=self.command,InstanceIds=['i-other'],DocumentName='AWS-RunShellScript'))
        with self.assertRaises(ValueError):self.run_submit(bad)
        self.assertTrue(self.receipt.exists())
        with self.assertRaises(ValueError):self.run_submit()
    def test_public_payload_is_encoded_and_has_exact_inventory(self):
        raw=json.dumps(dict(test='$(touch /nope); `exit`')).encode()
        scripts={name:'public script\n' for name in m.PUBLIC_SCRIPTS}
        command=m.build_command(raw,scripts,'set -eu\n',1790400000)
        self.assertNotIn('$(touch',command)
        encoded=re.search(r"b64decode\('([^']+)'\)",command).group(1)
        files=json.loads(gzip.decompress(base64.b64decode(encoded)))
        self.assertEqual(set(files),set(m.PUBLIC_SCRIPTS)|{'batch.json'});self.assertEqual(files['batch.json'].encode(),raw)
        self.assertIn('1790400000',command)
        with self.assertRaises(ValueError):m.build_command(raw,dict(scripts,private='forbidden'),'ready',1790400000)
        with self.assertRaises(ValueError):m.build_command(raw,scripts,'\nQSB_READY\n',1790400000)
