import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import test_proof_results as fixtures
from test_proof_results import r, s, ROOT

sys.path.insert(0,str(ROOT/'ops/fresh-proof'))
spec=importlib.util.spec_from_file_location('proof_collect',ROOT/'ops/fresh-proof/collect.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
INSTANCE='i-0123456789abcdef0'
ORIGINAL='00000000-0000-4000-8000-000000000001'
READ='00000000-0000-4000-8000-000000000002'

class CollectionTests(unittest.TestCase):
    def setUp(self):
        fixture=fixtures.ResultsTests();fixture.setUp()
        self.raw=fixture.raw;self.data,self.meta=fixture.encode()
        self.calls=[];self.pending=False;self.uncertain=False
    def aws(self,args):
        self.calls.append(args)
        if args[:2]==['ssm','send-command']:
            request=json.loads(args[3]);self.assertEqual(request['InstanceIds'],[INSTANCE])
            self.assertNotIn('docker',request['Parameters']['commands'][0])
            if self.uncertain:raise TimeoutError('unknown outcome')
            return {'Command':{'CommandId':READ}}
        cid=args[3]
        response=dict(CommandId=cid,InstanceId=INSTANCE,Status='Success',ResponseCode=0)
        if cid==ORIGINAL:
            response['StandardOutputContent']='QSB_PUBLIC_RESULT_META='+json.dumps(self.meta)
        else:
            response['Status']='InProgress' if self.pending else 'Success'
            response['StandardOutputContent']=self.data.decode()
        return response
    def run_collect(self,d,aws=None):
        return c.collect_once(Path(d)/'collection',INSTANCE,ORIGINAL,self.raw,aws or self.aws,
                              r.validate_batch,r.validate_binding,s.work_range)
    def test_collects_original_public_archive(self):
        with tempfile.TemporaryDirectory() as d:
            result=self.run_collect(d)
            self.assertFalse(result['grantsRangeCredit'])
            self.assertEqual(result['completedWorkerRows'],1)
            self.assertTrue((Path(d)/'collection/evidence/collection-receipt.json').exists())
    def test_pending_read_resumes_same_command(self):
        with tempfile.TemporaryDirectory() as d:
            self.pending=True
            self.assertEqual(self.run_collect(d)['status'],'waiting-for-chunk')
            self.pending=False
            self.run_collect(d)
            sends=[x for x in self.calls if x[1]=='send-command']
            self.assertEqual(len(sends),1)
    def test_unknown_submission_never_retried(self):
        with tempfile.TemporaryDirectory() as d:
            self.uncertain=True
            with self.assertRaises(TimeoutError):self.run_collect(d)
            self.uncertain=False
            with self.assertRaisesRegex(ValueError,'Uncertain'):self.run_collect(d)
            self.assertEqual(len([x for x in self.calls if x[1]=='send-command']),1)
    def test_other_instance_rejected_before_read(self):
        def wrong(args):
            response=self.aws(args);response['InstanceId']='i-11111111111111111';return response
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaisesRegex(ValueError,'identity'):self.run_collect(d,wrong)
            self.assertFalse(any(x[1]=='send-command' for x in self.calls))
    def test_original_pending_does_not_submit(self):
        def pending(args):return dict(CommandId=ORIGINAL,InstanceId=INSTANCE,Status='InProgress')
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(self.run_collect(d,pending)['status'],'waiting-for-original-command')
            self.assertEqual(self.calls,[])
    def test_missing_metadata_requires_reconciliation(self):
        def missing(args):return dict(CommandId=ORIGINAL,InstanceId=INSTANCE,Status='Failed',StandardOutputContent='')
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaisesRegex(ValueError,'Missing'):self.run_collect(d,missing)
    def test_changed_batch_cannot_reuse_collection(self):
        with tempfile.TemporaryDirectory() as d:
            self.pending=True;self.run_collect(d);self.raw+=b' '
            with self.assertRaisesRegex(ValueError,'context'):self.run_collect(d)
    def test_concurrent_local_collector_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            with patch.object(c.fcntl,'flock',side_effect=BlockingIOError('owned')):
                with self.assertRaises(BlockingIOError):self.run_collect(d)
            self.assertEqual(self.calls,[])
    def test_read_command_extracts_exact_public_bytes(self):
        import subprocess
        with tempfile.TemporaryDirectory() as d:
            archive=Path(d)/'public archive.b64';archive.write_bytes(self.data)
            output={}
            def transport(args):
                response=self.aws(args)
                if args[1]=='send-command':
                    request=json.loads(args[3])
                    output['text']=subprocess.check_output(request['Parameters']['commands'][0],shell=True,text=True)
                elif args[3]==READ:
                    response['StandardOutputContent']=output['text']
                return response
            with patch.object(c,'REMOTE',str(archive)):
                self.assertEqual(self.run_collect(d,transport)['completedWorkerRows'],1)
    def test_original_metadata_change_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            self.pending=True;self.run_collect(d)
            self.meta['sha256']='0'*64
            with self.assertRaisesRegex(ValueError,'archive changed'):self.run_collect(d)
    def test_truncated_success_does_not_publish_evidence(self):
        def truncated(args):
            response=self.aws(args)
            if args[1]=='get-command-invocation' and args[3]==READ:
                response['StandardOutputContent']=self.data[:-1].decode()
            return response
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaisesRegex(ValueError,'Truncated'):self.run_collect(d,truncated)
            self.assertFalse((Path(d)/'collection/evidence').exists())

    def test_cli_transport_has_no_hidden_retries(self):
        with patch.object(c.subprocess,'check_output',return_value='{}') as call:

            with patch.object(c, 'load_config', return_value={'profile':'test','region':'eu-west-1'}):
                c.aws_cli(['ssm','send-command'])
        self.assertEqual(call.call_args.kwargs['env']['AWS_MAX_ATTEMPTS'],'1')
        self.assertEqual(call.call_args.kwargs['timeout'],60)
        self.assertIn('--cli-read-timeout',call.call_args.args[0])
    def test_multiple_chunks_resume_pending_middle(self):
        import hashlib
        import re
        fixture=fixtures.ResultsTests();fixture.setUp()
        fixture.files['gate.log']=''.join(hashlib.sha256(str(i).encode()).hexdigest() for i in range(1000))
        self.data,self.meta=fixture.encode()
        self.assertGreater(len(self.data),2*c.CHUNK)
        reads={};poll_pending=[True]
        def transport(args):
            if args[1]=='send-command':
                request=json.loads(args[3]);code=request['Parameters']['commands'][0]
                start,end=map(int,re.search(r'd\[(\d+):(\d+)\]',code).groups())
                cid=f'00000000-0000-4000-8000-{len(reads)+10:012d}'
                reads[cid]=(start,end)
                return {'Command':{'CommandId':cid}}
            if args[3]==ORIGINAL:return self.aws(args)
            start,end=reads[args[3]]
            status='InProgress' if start==c.CHUNK and poll_pending[0] else 'Success'
            return dict(CommandId=args[3],InstanceId=INSTANCE,Status=status,ResponseCode=0,
                        StandardOutputContent=self.data[start:end].decode())
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(self.run_collect(d,transport)['offset'],c.CHUNK)
            self.assertEqual(len(reads),2)
            poll_pending[0]=False
            self.assertFalse(self.run_collect(d,transport)['grantsRangeCredit'])
            self.assertEqual(len(reads),(len(self.data)+c.CHUNK-1)//c.CHUNK)

    def test_scoped_cli_rejects_drift_between_identity_and_command(self):
        scope={'account':'123456789012','profile':'test','region':'eu-west-1'}
        with patch.object(c,'load_config',return_value=scope) as config, patch.object(c.subprocess,'check_output',return_value='{}') as call:
            aws=c.scoped_cli(scope)
            aws(['sts','get-caller-identity'])
            config.return_value=dict(scope,account='999999999999')
            for operation in ('send-command','get-command-invocation'):
                with self.assertRaisesRegex(ValueError,'operator scope changed'):
                    aws(['ssm',operation])
            self.assertEqual(call.call_count,1)
