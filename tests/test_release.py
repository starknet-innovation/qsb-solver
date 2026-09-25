import hashlib,json,pathlib,sys,tempfile,unittest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'scripts'))
from release_descriptor import descriptor, search_contract, ROOT
class ReleaseTests(unittest.TestCase):
    def test_exact_digest_binding(self):
        d=descriptor('a'*40,'sha256:'+'b'*64)
        self.assertEqual(d['solverCommit'],'a'*40)
        self.assertEqual(d['image'],'ghcr.io/starknet-innovation/qsb-solver@sha256:'+'b'*64)
        self.assertNotIn('sourceHashes',d)
    def test_invalid_identity(self):
        for commit,digest in [('main','sha256:'+'b'*64),('a'*40,'latest'),('a'*40,'sha256:'+'B'*64)]:
            with self.assertRaises(ValueError):descriptor(commit,digest)

    def test_contract_binding(self):
        value=json.loads((ROOT/'contracts/ranked-v2.json').read_text())
        expected=hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
        d=descriptor('a'*40,'sha256:'+'b'*64)
        self.assertEqual(d['schemaVersion'],3)
        self.assertEqual(d['searchContract'],expected)
        with tempfile.TemporaryDirectory() as tmp:
            path=pathlib.Path(tmp)/'contract.json'
            path.write_text(json.dumps(value,indent=4))
            self.assertEqual(search_contract(path),expected)
            value['cases'][0]['range']['count']+=1
            path.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError,'does not match'):
                search_contract(path)

    def test_invalid_contract_case_must_reject(self):
        value=json.loads((ROOT/'contracts/ranked-v2.json').read_text())
        value['invalid']=[{'stage':'pinning','attempt':0}]
        with tempfile.TemporaryDirectory() as tmp:
            path=pathlib.Path(tmp)/'contract.json'
            path.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError,'invalid case accepted'):
                search_contract(path)

    def test_missing_or_wrong_version_contract_rejected(self):
        original=json.loads((ROOT/'contracts/ranked-v2.json').read_text())
        for change in ({'searchVersion':'ranked-v1'},{'cases':[]},{'invalid':[]}):
            value={**original,**change}
            with self.subTest(change=change), tempfile.TemporaryDirectory() as tmp:
                path=pathlib.Path(tmp)/'contract.json'
                path.write_text(json.dumps(value))
                with self.assertRaisesRegex(ValueError,'Invalid search contract'):
                    search_contract(path)
