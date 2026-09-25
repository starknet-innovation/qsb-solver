import pathlib,sys,unittest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'scripts'))
from release_descriptor import descriptor
class ReleaseTests(unittest.TestCase):
    def test_exact_digest_binding(self):
        d=descriptor('a'*40,'sha256:'+'b'*64)
        self.assertEqual(d['solverCommit'],'a'*40)
        self.assertEqual(d['image'],'ghcr.io/starknet-innovation/qsb-solver@sha256:'+'b'*64)
        self.assertNotIn('sourceHashes',d)
    def test_invalid_identity(self):
        for commit,digest in [('main','sha256:'+'b'*64),('a'*40,'latest'),('a'*40,'sha256:'+'B'*64)]:
            with self.assertRaises(ValueError):descriptor(commit,digest)
