"""Execute full-unit host failure paths against fake system commands, without a GPU."""
import base64
import gzip
import json
import unittest
from tests import test_pqb_measure_host as measure_host


class FullUnitHostTest(unittest.TestCase):
    def setUp(self):
        measure_host.HostReceiptTest.setUp(self)
        (self.bundle / 'worker').mkdir()
        (self.bundle / 'worker/grind').write_text('simulated')
        (self.bundle / 'worker/grind').chmod(0o555)
        source = (measure_host.ROOT / 'ops/aws-gpu-execution/host-pqb-full-unit.sh').read_text()
        source = source.replace('/opt/qsb-pqb-full-unit', str(self.bundle)).replace(
            '/var/tmp/qsb-pqb-full-unit-results', str(self.results)).replace(
            '/run/qsb-shutdown-armed', str(self.root / 'armed'))
        self.script.write_text(source)

    def run_host(self, profile='pinning', **env):
        env.setdefault('FAKE_NOW', '1794399800')
        return measure_host.HostReceiptTest.run_host(self, profile, **env)

    def tearDown(self):
        self.temp.cleanup()

    def check_receipt(self, done, code):
        self.assertEqual(done.returncode, code, done.stdout + done.stderr)
        self.assertEqual((self.results / 'exit-code.txt').read_text(), str(code) + '\n')
        files = json.loads(gzip.decompress(base64.b64decode((self.results / 'public-result.b64').read_bytes())))
        self.assertEqual(files['exit-code.txt'], str(code) + '\n')
        return files

    def test_pull_failure_has_a_durable_receipt_and_does_not_run_compute(self):
        for code in (73, 124):
            with self.subTest(code=code):
                if self.results.exists():
                    import shutil
                    shutil.rmtree(self.results)
                files = self.check_receipt(self.run_host(FAKE_PULL_EXIT=str(code)), code)
                self.assertIn('image pull receipt', files['image-pull.log'])
                self.assertNotIn('invocation.json', files)

    def test_gpu_query_failure_has_a_durable_receipt(self):
        self.check_receipt(self.run_host(FAKE_GPU_EXIT='43'), 43)

    def test_insufficient_time_has_a_durable_receipt(self):
        files = self.check_receipt(self.run_host(FAKE_NOW='1794400990'), 1)
        self.assertNotIn('invocation.json', files)

    def test_success_records_the_stage_and_original_timeout(self):
        files = self.check_receipt(self.run_host(), 0)
        self.assertEqual(files['stage.txt'], 'pinning\n')
        self.assertEqual(json.loads(files['timeouts.json']), ['300', '1000'])
