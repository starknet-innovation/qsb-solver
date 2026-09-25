import copy
import importlib.util
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'worker/promotion/validation'))
spec=importlib.util.spec_from_file_location('perf_a10g',ROOT/'worker/promotion/validation/run_a10g_performance.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class PerformanceTests(unittest.TestCase):
    def setUp(self):
        self.row=dict(count=m.COUNT,rank=0,seconds=10.0,exit=0,log='[GPU 0] Done enum: 2147M in 10s',
                      summary=f'STATUS=EXHAUSTED 123 total_attempts={m.COUNT} elapsed_s=10 hits=0\n',hitFiles=[])
        self.result=dict(baselineSha256=m.BASELINE,candidateSha256=m.SUB,samples=[])
        for name in sorted(m.NAMES):
            for sample in range(3):
                for label in (('baseline','candidate') if sample%2==0 else ('candidate','baseline')):
                    self.result['samples'].append(dict(self.row,name=name,sample=sample,binary=label,seconds=10 if label=='baseline' else 5))
    def test_complete_paired_samples(self):
        s=m.summarize(self.result);self.assertEqual(len(s),4)
        self.assertTrue(all(v['throughputGainPercent']==100 for v in s.values()))
    def test_shortened_count_or_nonzero_hit_rejects(self):
        for suffix in [f'total_attempts={m.COUNT-1} elapsed_s=10 hits=0',f'total_attempts={m.COUNT} elapsed_s=10 hits=1']:
            with self.subTest(suffix=suffix),self.assertRaises(ValueError):m.check_sample(dict(self.row,summary='STATUS=EXHAUSTED 123 '+suffix))
    def test_timeout_error_duplicate_status_and_hit_files_reject(self):
        for summary in ['STATUS=TIMEOUT 123','STATUS=FOUND 123',self.row['summary']*2,'']:
            with self.subTest(summary=summary),self.assertRaises(ValueError):m.check_sample(dict(self.row,summary=summary))
        with self.assertRaises(ValueError):m.check_sample(dict(self.row,hitFiles=['digest_hit_0.txt']))
    def test_nonfinite_boolean_or_negative_times_reject(self):
        for seconds in [float('nan'),float('inf'),True,0,-1,121]:
            with self.subTest(seconds=seconds),self.assertRaises(ValueError):m.check_sample(dict(self.row,seconds=seconds))
    def test_incomplete_duplicate_and_wrong_order_reject(self):
        for samples in [self.result['samples'][:-1],self.result['samples']+[self.result['samples'][0]],list(reversed(self.result['samples']))]:
            with self.assertRaises(ValueError):m.summarize(dict(self.result,samples=samples))
    def test_wrong_binary_and_bad_completion_reject(self):
        with self.assertRaises(ValueError):m.summarize(dict(self.result,baselineSha256='0'*64))
        for log in ['',self.row['log']*2,self.row['log']+' QSB_RANGE_INCOMPLETE']:
            with self.assertRaises(ValueError):m.check_sample(dict(self.row,log=log))
    def test_real_process_summary_capture(self):
        import tempfile,base64,time
        with tempfile.TemporaryDirectory() as td:
            executable=Path(td)/'public-test';executable.write_text('#!/usr/bin/env python3\nfrom pathlib import Path\nPath("results").mkdir()\nPath("results/digest_summary_gpu0.txt").write_text('+repr(self.row['summary'])+')\nprint('+repr(self.row['log'])+')\n');executable.chmod(0o700)
            row=m.execute(executable,dict(params=base64.b64encode(b'public-test').decode(),sequence=1,locktime=2),time.monotonic()+10)
            self.assertEqual(row['summary'],self.row['summary']);self.assertEqual(row['exit'],0)
    def test_failed_process_retains_log_summary_and_hit(self):
        import tempfile,base64,time
        with tempfile.TemporaryDirectory() as td:
            executable=Path(td)/'public-test';executable.write_text('#!/usr/bin/env python3\nfrom pathlib import Path\nPath("results").mkdir()\nPath("results/digest_summary_gpu0.txt").write_text("STATUS=FOUND 123\\n")\nPath("results/digest_hit_0.txt").write_text("public-candidate")\nprint("partial diagnostic",flush=True)\n');executable.chmod(0o700)
            with self.assertRaises(m.SampleFailure) as caught:m.execute(executable,dict(params=base64.b64encode(b'public-test').decode(),sequence=1,locktime=2),time.monotonic()+10)
            self.assertIn('partial diagnostic',caught.exception.row['log'])
            self.assertEqual(caught.exception.row['hitFiles'],{'digest_hit_0.txt':'public-candidate'})
            self.assertIn('STATUS=FOUND',caught.exception.row['summary'])
    def test_timeout_retains_partial_output(self):
        import tempfile,base64,time
        with tempfile.TemporaryDirectory() as td:
            executable=Path(td)/'public-test';executable.write_text('#!/usr/bin/env python3\nimport time\nprint("before timeout",flush=True)\ntime.sleep(5)\n');executable.chmod(0o700)
            with self.assertRaises(m.SampleFailure) as caught:m.execute(executable,dict(params=base64.b64encode(b'public-test').decode(),sequence=1,locktime=2),time.monotonic()+0.5)
            self.assertTrue(caught.exception.row['timedOut'])
            self.assertIn('before timeout',caught.exception.row['log'])

    def test_full_range_projection_rejects_worker_timeout(self):
        result=copy.deepcopy(self.result)
        for row in result['samples']:
            if row['binary']=='candidate':row['seconds']=30
        with self.assertRaisesRegex(ValueError,'worker limit'):m.summarize(result)
    def test_projection_uses_slowest_sample_and_includes_startup(self):
        result=copy.deepcopy(self.result)
        result['samples'][1]['seconds']=6
        summary=m.summarize(result)
        first=sorted(m.NAMES)[0]
        self.assertEqual(summary[first]['projectedFullRangeSeconds']['candidate'],6*32)
