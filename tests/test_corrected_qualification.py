"""Collector rejection tests; these do not claim GPU execution."""
import importlib.util
from pathlib import Path
import unittest
import json
import tempfile

PATH = Path(__file__).resolve().parents[1]/'worker/promotion/validation/corrected_qualification.py'
spec = importlib.util.spec_from_file_location('corrected_qualification', PATH)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class CorrectedQualificationTests(unittest.TestCase):
    def test_exact_boundary_indices(self):
        self.assertEqual(m.unrank(0), list(range(9)))
        self.assertEqual(m.unrank(m.TOTAL-1), list(range(141,150)))
        self.assertEqual(len({tuple(m.unrank(n)) for n in range(125,135)}),10)
        for n in (-1,m.TOTAL):
            with self.assertRaises(ValueError):m.unrank(n)

    def test_complete_trace(self):
        expected={'0,1,2,3,4,5,6,7,8:0':'a'*64,'0,1,2,3,4,5,6,7,8:1':'b'*64}
        log='\n'.join(f'TRACE_SUB indices={key[:-2]} recid={key[-1]} hash={value}' for key,value in expected.items())
        self.assertEqual(m.verify_trace(log,expected),2)
        variants=[log.splitlines()[0],log+'\n'+log,log.replace('a'*64,'c'*64),log.replace('recid=1','recid=2'),log.replace('hash=','hash=x')]
        for changed in variants:
            with self.subTest(changed=changed):
                with self.assertRaises(ValueError):m.verify_trace(changed,expected)
        with self.assertRaises(ValueError):m.verify_trace(log,{})

    def test_trace_receipt_binds_exact_subset_and_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root/'trace-subset').write_bytes(b'trace')
            (root/'trace.diff').write_bytes(b'printf-only')
            receipt={'architecture':'sm_86','unmodifiedBinarySha256':'a'*64,
                     'files':{n:m.sha(root/n) for n in ('trace-subset','trace.diff')}}
            path=root/'receipt.json';path.write_text(json.dumps(receipt))
            binaries={'subset':(root/'unused','a'*64),'trace':(root/'trace-subset',m.sha(root/'trace-subset'))}
            self.assertEqual(m.validate_trace_receipt(path,binaries),receipt)
            binaries['subset']=(root/'unused','b'*64)
            with self.assertRaises(ValueError):m.validate_trace_receipt(path,binaries)
            binaries['subset']=(root/'unused','a'*64)
            (root/'trace.diff').write_bytes(b'changed')
            with self.assertRaises(ValueError):m.validate_trace_receipt(path,binaries)

    def test_trace_requires_every_expected_lane(self):
        with self.assertRaises(ValueError):m.verify_trace('[GPU 0] Done enum:', {'0,1,2,3,4,5,6,7,8:0':'a'*64})


if __name__=='__main__':unittest.main()
