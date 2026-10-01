import pathlib,re,unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
BUILDS=['worker/Dockerfile','worker/promotion/Dockerfile','worker/optimized/Dockerfile',
        '.github/workflows/ci.yml','.github/workflows/candidate.yml','.github/workflows/release.yml']
class TransportTests(unittest.TestCase):
    def test_runpod_transport_retired(self):
        for name in BUILDS+['worker/handler.py','worker/promotion/handler.py']:
            with self.subTest(file=name):
                self.assertNotIn('runpod',(ROOT/name).read_text().lower())
        self.assertFalse((ROOT/'worker/optimized/requirements.lock').exists())

    def test_only_aws_targets_built(self):
        for name in BUILDS[:3]:
            stages=re.findall(r'^FROM \S+ AS (\S+)',(ROOT/name).read_text(),re.M)
            with self.subTest(file=name):
                self.assertNotIn('queue',stages)
                if name!='worker/optimized/Dockerfile':self.assertEqual(stages[-1],'aws')

    def test_publishing_tags_are_aws_only(self):
        wf=ROOT/'.github/workflows'
        self.assertIn("tags: ['aws-v*']",(wf/'release.yml').read_text())
        self.assertIn("tags: ['candidate-sm86-*']",(wf/'candidate.yml').read_text())

if __name__=='__main__':unittest.main()
