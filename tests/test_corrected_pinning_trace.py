import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('pintrace',ROOT/'worker/promotion/validation/corrected_pinning_trace.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class PinTraceTests(unittest.TestCase):
    def test_only_diagnostic_inserted(self):
        source=(ROOT/'vendor/challenge/candidates/pinning/pinning.cu').read_text()
        result=m.instrument(source)
        self.assertEqual(source,''.join(line for line in result.splitlines(True) if 'TRACE_PIN sequence=' not in line))
        self.assertEqual(result.count('TRACE_PIN sequence='),1)
        self.assertIn('hs[7]);\n        int vv;',result)

    def test_changed_anchor_fails_closed(self):
        for value in ('','        int vv;\n        int vv;'):
            with self.assertRaises(ValueError):m.instrument(value)

    def test_complete_exact_trace(self):
        h='a'*64;key='2147483648:500000000:0'
        line='TRACE_PIN sequence=2147483648 locktime=500000000 recid=0 hash='+h
        self.assertEqual(m.verify_trace('noise\n'+line,{key:h}),1)
        for bad in ('',line+'\n'+line,line+' junk',line.replace('a'*64,'b'*64),line.replace('recid=0','recid=1')):
            with self.assertRaises(ValueError):m.verify_trace(bad,{key:h})

if __name__=='__main__':unittest.main()
