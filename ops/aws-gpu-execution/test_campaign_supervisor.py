import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('supervisor',Path(__file__).with_name('campaign_supervisor.py'))
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)

class Tests(unittest.TestCase):
    def test_upload_before_ack_and_exact_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'output';p=root/'range-00000000'/'record.json';p.parent.mkdir(parents=True)
            p.write_text(json.dumps({'status':'compute-intent','binding':'a'*64,'attempt':0}))
            ack=Path(tmp)/'ack';calls=[]
            def put(_):
                self.assertFalse(ack.exists());calls.append('upload')
            self.assertTrue(s.acknowledge(root,ack,p,put))
            value=json.loads(next(ack.glob('*.json')).read_text())
            self.assertEqual(value,{'recordPath':'range-00000000/record.json','recordSha256':s.hashlib.sha256(p.read_bytes()).hexdigest(),'binding':'a'*64})
            self.assertFalse(s.acknowledge(root,ack,p,put));self.assertEqual(calls,['upload'])
    def test_failed_upload_cannot_ack(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);p=root/'range-00000000'/'record.json';p.parent.mkdir();p.write_text(json.dumps({'status':'compute-intent','binding':'b'*64,'attempt':0}))
            def fail(_):raise RuntimeError('test')
            with self.assertRaises(RuntimeError):s.acknowledge(root,root/'ack',p,fail)
            self.assertFalse((root/'ack').exists())
    def test_snapshot_rejects_symlink_and_size(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'root';root.mkdir();(root/'x').write_text('public')
            with patch.object(s,'MAX_BYTES',1):
                with self.assertRaises(ValueError):s.snapshot(root,Path(tmp)/'a.tgz')
            (root/'link').symlink_to(root/'x')
            with self.assertRaises(ValueError):s.snapshot(root,Path(tmp)/'a.tgz')
    def test_upload_error_redacts_capability(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(s.urllib.request,'urlopen',side_effect=Exception('secret-query')):
            with self.assertRaises(RuntimeError) as e:s.upload(Path(tmp),'https://example.test/?secret-query')
            self.assertNotIn('secret',str(e.exception))
    def test_prepare_timeout_cleans_and_checkpoints_without_execution(self):
        command=['docker','run','--network=none','--read-only','--name=x','image@sha256:'+'a'*64]
        with tempfile.TemporaryDirectory() as tmp, patch.object(s.subprocess,'run',side_effect=s.subprocess.TimeoutExpired('docker',120)) as calls, patch.object(s,'upload') as put:
            with self.assertRaises(s.subprocess.TimeoutExpired):
                s.supervise(Path(tmp)/'root',Path(tmp)/'acks',command,9999999999,'https://example.test','x')
            self.assertEqual(calls.call_count,2)
            self.assertEqual(calls.call_args_list[0].args[0][-1],'prepare')
            self.assertEqual(calls.call_args_list[1].args[0],['docker','rm','-f','x'])
            put.assert_called_once()

    def test_networked_command_rejected_before_launch(self):
        with tempfile.TemporaryDirectory() as tmp,patch.object(s.subprocess,'run') as run:
            with self.assertRaises(ValueError):s.supervise(Path(tmp),Path(tmp)/'ack',['docker','run'],9999999999,'https://example.test','x')
            run.assert_not_called()

if __name__=='__main__':unittest.main()
