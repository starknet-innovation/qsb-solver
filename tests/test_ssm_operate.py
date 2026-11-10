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
        (p/'execution.json').write_text(json.dumps(dict(operatorConfig=config,instanceId='i-test',deadline=int(time.time())+1500)))
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
                self.assertTrue(1020<=timeout<=1440,timeout)
                return json.dumps({'Command':{'CommandId':'cmd-test'}})
            self.invoke(p,'send',fake)
            self.assertTrue((p/'send-response.json').exists())
            with self.assertRaises(AssertionError):self.invoke(p,'send',fake)
