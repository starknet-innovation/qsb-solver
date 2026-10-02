"""Exercise real child-process collection with inert scripts, not CUDA binaries."""
import base64
from pathlib import Path
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'experiments/generic-sha-vector'))
from run_pair import execute, SampleFailure


class ProcessTests(unittest.TestCase):
    def run_script(self, body, seconds=5):
        with tempfile.TemporaryDirectory() as directory:
            binary=Path(directory)/'inert-solver'
            binary.write_text('#!'+sys.executable+'\n'+body)
            binary.chmod(0o700)
            fixture=dict(params=base64.b64encode(b'public synthetic bytes').decode(), sequence=1, locktime=0)
            return execute(binary, fixture, time.monotonic()+seconds, count=257, rank=63)

    def success_body(self):
        return '''from pathlib import Path
import sys
assert sys.argv[-2:] == ['rank_start=63','rank_count=257']
Path('results').mkdir()
Path('results/digest_summary_gpu0.txt').write_text('STATUS=EXHAUSTED 1 total_attempts=257 elapsed_s=0 hits=0\\n')
print('[GPU 0] Done enum:')
'''

    def test_real_process_complete_custom_range(self):
        row=self.run_script(self.success_body())
        self.assertEqual((row['rank'],row['count'],row['exit']),(63,257,0))

    def test_real_process_failures_retain_output(self):
        for suffix in ["raise SystemExit(2)",
                       "Path('results/digest_hit_0.txt').write_text('unverified')",
                       "Path('results/digest_summary_gpu0.txt').write_text('STATUS=EXHAUSTED 1 total_attempts=256 elapsed_s=0 hits=0')"]:
            with self.subTest(suffix=suffix), self.assertRaises(SampleFailure) as caught:
                self.run_script(self.success_body()+suffix+'\n')
            self.assertIn('[GPU 0] Done enum:',caught.exception.row['log'])
            self.assertTrue(caught.exception.row['failureReason'])

    def test_timeout_kills_child_and_retains_diagnostics(self):
        with self.assertRaises(SampleFailure) as caught:
            self.run_script("import time\nprint('started',flush=True)\ntime.sleep(30)\n",seconds=0.5)
        self.assertTrue(caught.exception.row['timedOut'])
        self.assertNotEqual(caught.exception.row['exit'],0)
        self.assertIn('started',caught.exception.row['log'])
