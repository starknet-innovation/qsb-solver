import pathlib,re,sys,unittest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'scripts'))
from image_scan import GRYPE_SHA256, GRYPE_VERSION, evaluate, trimmed
ROOT=pathlib.Path(__file__).resolve().parents[1]

def match(cve,pkg,severity,fix='fixed',related=()):
    return {'vulnerability':{'id':cve,'severity':severity,'fix':{'state':fix,'versions':['2'] if fix=='fixed' else []}},
            'relatedVulnerabilities':[{'id':cve,'namespace':'nvd:cpe','severity':s} for s in related],
            'artifact':{'name':pkg,'version':'1','type':'deb'}}

class ImageScanTests(unittest.TestCase):
    def test_nvd_critical_blocks_when_distro_rates_lower(self):
        s=evaluate({'matches':[match('CVE-1','openssl','Medium',related=['Critical'])]})
        self.assertFalse(s['passed'])
        self.assertEqual([b['id'] for b in s['blocking']],['CVE-1'])
        self.assertEqual(s['counts']['Critical'],{'total':1,'fixable':1})

    def test_unfixed_critical_reported_not_blocking(self):
        s=evaluate({'matches':[match('CVE-2','python3-pip','Critical',fix='not-fixed'),match('CVE-3','perl-base','High',fix='wont-fix')]})
        self.assertTrue(s['passed'])
        self.assertEqual([u['package'] for u in s['unfixedCritical']],['python3-pip'])
        self.assertEqual(s['counts']['High'],{'total':1,'fixable':0})

    def test_fixable_high_does_not_block(self):
        self.assertTrue(evaluate({'matches':[match('CVE-4','libc6','High',related=['High'])]})['passed'])

    def test_runtime_configuration_not_retained(self):
        r=trimmed({'matches':[],'descriptor':{'name':'grype','version':GRYPE_VERSION,'configuration':{'registry':{'auth':['x']}}}})
        self.assertNotIn('configuration',r['descriptor'])

    def test_scanner_pinned_by_version_and_hash(self):
        self.assertRegex(GRYPE_VERSION,r'^\d+\.\d+\.\d+$')
        self.assertTrue(all(re.fullmatch('[0-9a-f]{64}',h) for h in GRYPE_SHA256.values()))

    def test_publishing_workflows_scan_before_release(self):
        for name,before,after in [('candidate.yml','image_scan.py','docker push'),
                                  ('release.yml','image_scan.py','Attest image'),
                                  ('release.yml','image_scan.py','Produce consumer descriptor')]:
            text=(ROOT/'.github/workflows'/name).read_text()
            with self.subTest(workflow=name,step=after):
                self.assertLess(text.index(before),text.index(after))
                self.assertIn('image-scan/image-scan.json',text)

if __name__=='__main__':unittest.main()
