import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ops/fresh-proof'))
import publication as p

class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        (self.root/'evidence').mkdir();self.raw=b'{"public":"batch"}'
        self.instance='i-12345678901234567';self.command='11111111-1111-4111-8111-111111111111';self.text='frozen reviewed public command'
        self.context=dict(instanceId=self.instance,commandId=self.command,batchSha256=hashlib.sha256(self.raw).hexdigest())
        self.meta=dict(bytes=100,sha256='a'*64)
        self.save('context.json',self.context);self.save('metadata.json',self.meta);self.save('evidence/collection-receipt.json',dict(archive=self.meta))
        (self.root/'evidence/batch.json').write_bytes(self.raw)
        self.provider=dict(CommandId=self.command,InstanceIds=[self.instance],DocumentName='AWS-RunShellScript',Parameters=dict(commands=[self.text]),Status='Success')
        self.inv=dict(CommandId=self.command,InstanceId=self.instance,Status='Success',ResponseCode=0,StandardOutputContent='QSB_PUBLIC_RESULT_META='+json.dumps(self.meta))
        self.calls=[]
    def save(self,name,value):(self.root/name).write_text(json.dumps(value))
    def aws(self,args):
        self.calls.append(args)
        return dict(Commands=[self.provider]) if args[1]=='list-commands' else self.inv
    def check(self):
        return p.EvidenceVerifier(self.root,self.root/'fixture','b'*64,self.root/'reference',self.aws)(self.raw,dict(instanceId=self.instance),self.command,self.text)
    def test_exact_provider_and_collection_bind_before_cpu(self):
        with patch.object(p,'verify_collection',return_value=dict(grantsRangeCredit=False)) as cpu:
            result=self.check();cpu.assert_called_once_with(self.root/'evidence',self.root/'fixture','b'*64,self.root/'reference')
        self.assertEqual(result['providerBinding'],self.context)
        self.assertEqual([a[1] for a in self.calls],['list-commands','get-command-invocation'])
    def test_wrong_command_or_instance_cannot_reach_cpu(self):
        for key,value in [('CommandId','other'),('InstanceIds',['i-other']),('Parameters',dict(commands=['substituted'])),('Status','Failed')]:
            old=self.provider[key];self.provider[key]=value
            with self.subTest(key=key),patch.object(p,'verify_collection') as cpu,self.assertRaises(ValueError):self.check()
            cpu.assert_not_called();self.provider[key]=old
    def test_mismatched_archive_or_unsuccessful_invocation_rejects(self):
        for key,value in [('Status','InProgress'),('ResponseCode',2),('StandardOutputContent','QSB_PUBLIC_RESULT_META={"bytes":99}')]:
            old=self.inv[key];self.inv[key]=value
            with self.subTest(key=key),patch.object(p,'verify_collection') as cpu,self.assertRaises(ValueError):self.check()
            cpu.assert_not_called();self.inv[key]=old
    def test_changed_context_or_batch_rejects_before_aws(self):
        self.save('context.json',dict(self.context,commandId='other'))
        with self.assertRaises(ValueError):self.check()
        self.save('context.json',self.context);(self.root/'evidence/batch.json').write_bytes(b'changed')
        with self.assertRaises(ValueError):self.check()
        self.assertEqual(self.calls,[])
    def test_cpu_failure_propagates(self):
        with patch.object(p,'verify_collection',side_effect=ValueError('tampered evidence')),self.assertRaisesRegex(ValueError,'tampered'):
            self.check()
    def test_wrong_document_invocation_identity_and_duplicate_metadata(self):
        self.provider['DocumentName']='unexpected-document'
        with self.assertRaises(ValueError):self.check()
        self.provider['DocumentName']='AWS-RunShellScript'
        for key,value in [('CommandId','other'),('InstanceId','i-other'),('StandardOutputContent',self.inv['StandardOutputContent']+'\n'+self.inv['StandardOutputContent'])]:
            old=self.inv[key];self.inv[key]=value
            with self.subTest(key=key),patch.object(p,'verify_collection') as cpu,self.assertRaises(ValueError):self.check()
            cpu.assert_not_called();self.inv[key]=old
