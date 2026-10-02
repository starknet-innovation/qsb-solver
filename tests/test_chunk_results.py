import base64
import gzip
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'ops/aws-gpu-execution'))
from chunk_results import collect, decode, metadata

class ChunkResultsTests(unittest.TestCase):
    def envelope(self, value):
        data=base64.b64encode(gzip.compress(json.dumps(value).encode()))
        meta={'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
        return data,meta

    def test_decode_and_reject_corruption(self):
        data,meta=self.envelope({'result.json':'public result'})
        self.assertEqual(decode(data,meta),{'result.json':'public result'})
        with self.assertRaises(ValueError):decode(data+b'A',meta)
        with self.assertRaises(ValueError):metadata('')
        line='QSB_PUBLIC_RESULT_META='+json.dumps(meta)
        with self.assertRaises(ValueError):metadata(line+'\n'+line)
        self.assertEqual(metadata(line),meta)

    def test_paths_and_size_rejected(self):
        data,meta=self.envelope({'../escape':'x'})
        with self.assertRaises(ValueError):decode(data,meta)
        data,meta=self.envelope({'log':'x'*8000001})
        with self.assertRaises(ValueError):decode(data,meta)

    def test_collect_resume_and_identity(self):
        data,meta=self.envelope({'result.json':'a public result'})
        row={'CommandId':'c','InstanceId':'i','Status':'Success','ResponseCode':0,'StandardOutputContent':data.decode()}
        calls=[]
        def aws(*args):
            calls.append(args)
            return {'Command':{'CommandId':'c'}} if args[1]=='send-command' else row
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'chunks';out='QSB_PUBLIC_RESULT_META='+json.dumps(meta)
            self.assertEqual(collect(p,'i',out,aws,time.time()+600,sleep=lambda _:None),{'result.json':'a public result'})
            before=len(calls)
            collect(p,'i',out,aws,time.time()+600,sleep=lambda _:None)
            self.assertEqual(len(calls),before)
            r=json.loads((p/'0-result.json').read_text());r['InstanceId']='wrong'
            (p/'0-result.json').write_text(json.dumps(r))
            with self.assertRaises(ValueError):collect(p,'i',out,aws,time.time()+600)

    def test_multiple_chunks_and_truncation(self):
        import random
        value={'log':random.Random(7).randbytes(50000).hex()}
        data,meta=self.envelope(value)
        self.assertGreater(len(data),18000)
        sends=[]
        def aws(*args):
            if args[1]=='send-command':
                cid=str(len(sends));sends.append(cid)
                return {'Command':{'CommandId':cid}}
            cid=args[args.index('--command-id')+1];start=int(cid)*18000
            return {'CommandId':cid,'InstanceId':'i','Status':'Success','ResponseCode':0,
                    'StandardOutputContent':data[start:start+18000].decode()}
        with tempfile.TemporaryDirectory() as tmp:
            result=collect(Path(tmp)/'chunks','i','QSB_PUBLIC_RESULT_META='+json.dumps(meta),aws,time.time()+600,sleep=lambda _:None)
            self.assertEqual(result,value)
            self.assertEqual(len(sends),(len(data)+17999)//18000)

    def test_uncertain_send_never_retried(self):
        data,meta=self.envelope({'x':'y'});calls=[]
        def fail(*args):calls.append(args);raise RuntimeError('ambiguous')
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'chunks';out='QSB_PUBLIC_RESULT_META='+json.dumps(meta)
            with self.assertRaises(RuntimeError):collect(p,'i',out,fail,time.time()+600,sleep=lambda _:None)
            with self.assertRaises(ValueError):collect(p,'i',out,fail,time.time()+600,sleep=lambda _:None)
            self.assertEqual(len(calls),1)

if __name__=='__main__':unittest.main()
