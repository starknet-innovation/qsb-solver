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
            p=Path(d);self.setup_state(p);(p/'host-template.sh').write_text('set -euo pipefail\necho __DEADLINE__')
            def fake(args,**kwargs):
                if 'get-caller-identity' in args:return json.dumps({'Account':'123'})
                self.assertIn('send-command',args)
                intent=json.loads((p/'send-intent.json').read_text())
                command=intent['request']['Parameters']['commands'][0]
                self.assertTrue(command.startswith("exec /bin/bash -s <<'"))
                self.assertNotIn('__DEADLINE__',command)
                return json.dumps({'Command':{'CommandId':'cmd-test'}})
            self.invoke(p,'send',fake)
            self.assertTrue((p/'send-response.json').exists())
            with self.assertRaises(AssertionError):self.invoke(p,'send',fake)
