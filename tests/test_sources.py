import hashlib, importlib.util, json, pathlib, subprocess, sys, unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
class SourceTests(unittest.TestCase):
    def test_historical_import(self):
        base=ROOT/'vendor/challenge'
        p=json.loads((base/'provenance.json').read_text())
        self.assertEqual(p['commit'],'2791ed0588f5014ccd688d48ba5502df2879f2f1')
        actual={str(x.relative_to(base)) for x in base.rglob('*') if x.is_file() and x.name!='provenance.json'}
        self.assertEqual(actual,set(p['files']))
        for n,h in p['files'].items(): self.assertEqual(hashlib.sha256((base/n).read_bytes()).hexdigest(),h,n)
    def test_optimized_source_lock(self):
        base=ROOT/'research/optimized-subset'
        lock=json.loads((ROOT/'worker/optimized/source-lock.json').read_text())
        self.assertEqual({str(p.relative_to(base)) for p in (base/'subset').rglob('*') if p.is_file()},set(lock['files']))
        for n,h in lock['files'].items(): self.assertEqual(hashlib.sha256((base/n).read_bytes()).hexdigest(),h,n)
    def test_historical_adaptation_preserved(self):
        subprocess.run([sys.executable,str(ROOT/'worker/prepare_kernels.py')],check=True,capture_output=True)
        subset=(ROOT/'worker/build/subset/tests/gpu_epochs/tree.cu').read_text()
        pin=(ROOT/'worker/build/pinning/pinning.cu').read_text()
        for text in [subset,pin]:
            self.assertIn('? 64 :',text)
            self.assertNotIn('QSB_RANGE_INCOMPLETE: hit count exceeds host capacity',text)
            self.assertNotIn('hand exceptional active points',text)
        self.assertIn('return gpu_is_valid_der(digest, 32);',subset)
        self.assertIn('if(!usable)return;',subset)
        optimized=(ROOT/'research/optimized-subset/subset/tests/gpu_epochs/tree.cu').read_text()
        self.assertIn('hand exceptional active points',optimized)
    def test_no_independent_verifier(self):
        self.assertFalse((ROOT/'worker/cpu').exists())
        self.assertFalse((ROOT/'worker/optimized/reference').exists())
    def test_worker_rejects_private_fields(self):
        sys.path.insert(0,str(ROOT/'worker'))
        import handler
        with self.assertRaisesRegex(ValueError,'private fields'):handler.validate_request({'passphrase':'public-test-value'})
    def test_pqb_import(self):
        base=ROOT/'vendor/pqb'
        p=json.loads((base/'provenance.json').read_text())
        self.assertEqual(p['commit'],'eccdd09772edf14ab37fc63992b0626ad7ff2221')
        actual={str(x.relative_to(base)) for x in base.rglob('*') if x.is_file() and x.name!='provenance.json'}
        self.assertEqual(actual,set(p['files']))
        for n,h in p['files'].items(): self.assertEqual(hashlib.sha256((base/n).read_bytes()).hexdigest(),h,n)
    def test_pqb_ranked_source_lock(self):
        lock=json.loads((ROOT/'research/pqb-ranked/source-lock.json').read_text())
        p=json.loads((ROOT/'vendor/pqb/provenance.json').read_text())
        self.assertEqual(lock['status'],'HOLD')
        self.assertEqual(lock['upstream']['commit'],p['commit'])
        self.assertEqual(lock['upstream']['adaptedFromSha256'],p['files']['grinder/grind.cu'])
        for n,h in lock['sources'].items(): self.assertEqual(hashlib.sha256((ROOT/n).read_bytes()).hexdigest(),h,n)
        # the adaptation is a different file from upstream and says so; the headers are upstream's
        self.assertNotEqual(lock['sources']['research/pqb-ranked/grind.cu'],p['files']['grinder/grind.cu'])
        self.assertIn('NOT the unchanged upstream file',(ROOT/'research/pqb-ranked/grind.cu').read_text())
    def test_pqb_is_not_in_the_qsb_images(self):
        for dockerfile in ('worker/Dockerfile','worker/optimized/Dockerfile','worker/promotion/Dockerfile'):
            self.assertNotIn('pqb',(ROOT/dockerfile).read_text().lower(),dockerfile)
        for workflow in ('release.yml','candidate.yml','aws-worker.yml'):
            self.assertNotIn('pqb',(ROOT/'.github/workflows'/workflow).read_text().lower(),workflow)
