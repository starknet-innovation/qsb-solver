import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent))
import campaign_pipeline as p
import json
import tempfile
import unittest
from unittest.mock import patch

class Tests(unittest.TestCase):
    def test_readonly_ack_and_exact_runtime(self):
        name,args=p.command(Path('/bundle'),Path('/out'),Path('/ack'),'round1',123,Path('/pin.json'))
        self.assertIn('/ack:/acks:ro',args);self.assertIn(p.IMAGE,args)
        self.assertIn('/pin.json:/solution.json:ro',args)
        self.assertIn('--name='+name,args)
        self.assertEqual(args[-4:],['--solution','/solution.json','--stage','round1'])
    def test_capability_paths_cannot_enter_snapshot_or_container(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(p,'supervise') as run:
            root=Path(tmp)
            for urls in (root/'bundle'/'urls',root/'output'/'urls',root):
                with self.assertRaises(ValueError):p.run(root/'bundle',root/'output',urls,123)
            run.assert_not_called()
    def test_all_stages_require_verified_hit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle=root/'bundle';bundle.mkdir();urls=root/'urls';urls.mkdir()
            for stage in ['pinning','round1','round2']:(urls/(stage+'.url')).write_text('https://example.test')
            calls=[]
            def stage(output,acks,args,*rest):
                calls.append(output.name)
                (output/'solution.json').write_text(json.dumps({'test':output.name}))
                return {'status':'verified-hit'}
            with patch.object(p,'supervise',side_effect=stage):result=p.run(bundle,root/'output',urls,123)
            self.assertEqual(calls,['pinning','round1','round2']);self.assertEqual(result['status'],'all-puzzles-cpu-verified')
    def test_partial_stops_without_next_stage(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'bundle').mkdir();(root/'urls').mkdir();(root/'urls'/'pinning.url').write_text('https://example.test')
            with patch.object(p,'supervise',return_value={'status':'deadline-stop'}) as run:
                result=p.run(root/'bundle',root/'out',root/'urls',123)
            run.assert_called_once();self.assertEqual(result['status'],'partial-stop')

if __name__=='__main__':unittest.main()
