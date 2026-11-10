import json
from pathlib import Path
import runpy
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
OPS=ROOT/'ops/aws-gpu-execution'

class OperateTests(unittest.TestCase):
    def setup_state(self,p):
        config=dict(profile='test',region='eu-west-2',account='123')
        (p/'operator.json').write_text(json.dumps(config))
        (p/'execution.json').write_text(json.dumps(dict(operatorConfig=config,instanceId='i-test',deadline=int(time.time())+2000)))
    def stage(self,p,text='set -euo pipefail\necho __DEADLINE__'):
        import hashlib
        (p/'host-template.sh').write_text(text)
        (p/'host-template.sh.sha256').write_text(hashlib.sha256(text.encode()).hexdigest()+'\n')
    def refuse(self,args,**kwargs):
        if 'get-caller-identity' in args:return json.dumps({'Account':'123'})
        self.fail('unexpected call: '+str(args))
    def test_unstaged_or_changed_template_is_never_sent(self):
        for change in ('missing-digest','edited-template'):
            with self.subTest(change=change),tempfile.TemporaryDirectory() as d:
                p=Path(d);self.setup_state(p);self.stage(p)
                if change=='missing-digest':(p/'host-template.sh.sha256').unlink()
                else:(p/'host-template.sh').write_text('echo replaced')
                with self.assertRaises((ValueError,FileNotFoundError)):self.invoke(p,'send',self.refuse)
                self.assertFalse((p/'send-intent.json').exists())
    def test_send_reserves_staging_time(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);self.setup_state(p);self.stage(p)
            state=json.loads((p/'execution.json').read_text());state['deadline']=int(time.time())+1400
            (p/'execution.json').write_text(json.dumps(state))
            with self.assertRaises(AssertionError):self.invoke(p,'send',self.refuse)
            self.assertFalse((p/'send-intent.json').exists())
    def test_interrupted_terminal_poll_resumes_and_still_terminates(self):
        import base64,gzip
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);self.setup_state(p)
            (p/'send-response.json').write_text(json.dumps({'Command':{'CommandId':'cmd-test'}}))
            body=base64.b64encode(gzip.compress(json.dumps({'result.json':'{}'}).encode())).decode()
            import hashlib
            out='RESULT_SHA256='+hashlib.sha256(body.encode()).hexdigest()+'\nRESULT_BASE64='+body+'\n'
            invocation=dict(CommandId='cmd-test',InstanceId='i-test',Status='Success',ResponseCode=0,StandardOutputContent=out,StandardErrorContent='')
            # The earlier run stored the terminal receipt, then stopped before collecting or terminating.
            (p/'terminal.json').write_text(json.dumps(invocation))
            calls=[]
            def fake(args,**kwargs):
                calls.append(args)
                if 'get-caller-identity' in args:return json.dumps({'Account':'123'})
                if 'get-command-invocation' in args:return json.dumps(invocation)
                if 'terminate-instances' in args:return json.dumps({'TerminatingInstances':[{'InstanceId':'i-test'}]})
                self.fail(str(args))
            self.invoke(p,'poll',fake)
            self.assertEqual(json.loads((p/'public-results.json').read_text()),{'result.json':'{}'})
            self.assertTrue((p/'terminate-response.json').exists())
            self.invoke(p,'poll',fake)
            self.assertEqual(sum('terminate-instances' in a for a in calls),2)
            (p/'terminal.json').write_text(json.dumps(dict(invocation,Status='Failed')))
            with self.assertRaises(ValueError):self.invoke(p,'poll',fake)
    def test_record_replaces_state_atomically_and_keeps_identities(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);self.setup_state(p)
            state=json.loads((p/'execution.json').read_text());state.update(token='tok',name='qsb-bench-test',securityGroup='sg-test')
            (p/'execution.json').write_text(json.dumps(state))
            instance=dict(InstanceId='i-test',ClientToken='tok',InstanceType='g5.xlarge',State={'Name':'running'},BlockDeviceMappings=[{'Ebs':{'VolumeId':'vol-test'}}])
            def fake(args,**kwargs):
                if 'get-caller-identity' in args:return json.dumps({'Account':'123'})
                if 'describe-instances' in args:return json.dumps({'Reservations':[{'Instances':[instance]}]})
                self.fail(str(args))
            self.invoke(p,'record',fake)
            after=json.loads((p/'execution.json').read_text())
            self.assertEqual(after['volumeIds'],['vol-test'])
            self.assertEqual({k:after[k] for k in state},state)
            self.assertFalse((p/'execution.json.tmp').exists())
            # A failure while writing the replacement leaves the original state intact.
            (p/'allocated.json').unlink()
            before=(p/'execution.json').read_text()
            with patch('os.replace',side_effect=OSError('interrupted')),self.assertRaises(OSError):self.invoke(p,'record',fake)
            self.assertEqual((p/'execution.json').read_text(),before)
    def test_record_resumes_only_for_the_same_allocation(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);self.setup_state(p)
            state=json.loads((p/'execution.json').read_text());state.update(token='tok');(p/'execution.json').write_text(json.dumps(state))
            def reservation(volume,instance='i-test'):
                return {'Reservations':[{'Instances':[dict(InstanceId=instance,ClientToken='tok',InstanceType='g5.xlarge',State={'Name':'running'},BlockDeviceMappings=[{'Ebs':{'VolumeId':volume}}])]}]}
            def fake(args,**kwargs):
                if 'get-caller-identity' in args:return json.dumps({'Account':'123'})
                if 'describe-instances' in args:return json.dumps(reservation('vol-test'))
                self.fail(str(args))
            # The earlier run stored the receipt, then stopped before updating the state.
            (p/'allocated.json').write_text(json.dumps(reservation('vol-test')))
            self.invoke(p,'record',fake)
            self.assertEqual(json.loads((p/'execution.json').read_text())['volumeIds'],['vol-test'])
            for other in (reservation('vol-other'),reservation('vol-test','i-other')):
                (p/'allocated.json').write_text(json.dumps(other))
                with self.assertRaises(ValueError):self.invoke(p,'record',fake)
    def test_launch_minimum_covers_the_send_gate_and_host_gate(self):
        import re
        number=lambda path,pattern:int(re.search(pattern,(ROOT/path).read_text()).group(1))
        send=number('ops/aws-gpu-execution/operate.py',r'MIN_SEND_SECONDS=(\d+)')
        control=(ROOT/'ops/aws-gpu-execution/control.py').read_text()
        self.assertIn('MIN_LAUNCH_SECONDS = %d + 300'%send,control)
        self.assertIn("<MIN_LAUNCH_SECONDS: raise ValueError('Insufficient time before deadline')",control)
        host=(ROOT/'experiments/sha-rotate-add/host-full.sh').read_text()
        before,after=[int(x) for x in re.findall(r'-ge (\d+) \]',host)]
        self.assertEqual((before,after),(1200,900))
        self.assertGreaterEqual(after,720+120+60)      # gate timeout, collector reserve, packaging
        self.assertGreaterEqual(before,after+300)      # image pull limit
        self.assertGreaterEqual(send,before+420)       # staging reserve
    def test_unknown_mode_fails_before_any_call(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);self.setup_state(p)
            def fake(args,**kwargs):self.fail('no call expected: '+str(args))
            with self.assertRaises(SystemExit) as caught:self.invoke(p,'terminte',fake)
            self.assertIn('usage',str(caught.exception))
    def invoke(self,p,mode,fake):
        with patch.object(sys,'argv',['operate.py',str(p),mode]),patch.object(sys,'path',[str(OPS),*sys.path]),patch('subprocess.check_output',side_effect=fake):
            runpy.run_path(str(OPS/'operate.py'),run_name='__main__')
    def test_early_shell_failure_preserves_diagnostics_and_terminates(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);self.setup_state(p)
            (p/'send-response.json').write_text(json.dumps({'Command':{'CommandId':'cmd-test'}}))
            calls=[]
            def fake(args,**kwargs):
                calls.append(args)
                if 'get-caller-identity' in args:return json.dumps({'Account':'123'})
                if 'get-command-invocation' in args:return json.dumps(dict(CommandId='cmd-test',InstanceId='i-test',Status='Failed',ResponseCode=2,StandardOutputContent='',StandardErrorContent='set: Illegal option -o pipefail'))
                if 'terminate-instances' in args:return json.dumps({'TerminatingInstances':[{'InstanceId':'i-test'}]})
                self.fail(str(args))
            self.invoke(p,'poll',fake)
            self.assertEqual(json.loads((p/'terminal.json').read_text())['ResponseCode'],2)
            self.assertIn('missing',json.loads((p/'collection-error.json').read_text())['error'])
            self.assertTrue((p/'terminate-response.json').exists())
            self.assertEqual(sum('terminate-instances' in a for a in calls),1)
            self.assertFalse((p/'public-results.json').exists())
    def test_submission_intent_contains_explicit_bash_before_send(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);self.setup_state(p);self.stage(p)
            def fake(args,**kwargs):
                if 'get-caller-identity' in args:return json.dumps({'Account':'123'})
                self.assertIn('send-command',args)
                intent=json.loads((p/'send-intent.json').read_text())
                command=intent['request']['Parameters']['commands'][0]
                self.assertTrue(command.startswith("exec /bin/bash -s <<'"))
                self.assertNotIn('__DEADLINE__',command)
                timeout=int(intent['request']['Parameters']['executionTimeout'][0])
                self.assertEqual(timeout,1800)
                return json.dumps({'Command':{'CommandId':'cmd-test'}})
            self.invoke(p,'send',fake)
            self.assertTrue((p/'send-response.json').exists())
            with self.assertRaises(AssertionError):self.invoke(p,'send',fake)
