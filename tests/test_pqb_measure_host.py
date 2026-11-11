"""Run the real host script against simulated system commands. No AWS, Docker or GPU."""
import base64
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FAKE = r'''
import hashlib,json,os,pathlib,sys
name=pathlib.Path(sys.argv[0]).name
args=sys.argv[1:]
results=pathlib.Path(os.environ['FAKE_RESULTS'])
if name=='sha256sum':
 if args[0]=='-c':
  for line in pathlib.Path(args[1]).read_text().splitlines():
   want,file=line.split('  ',1)
   if hashlib.sha256(pathlib.Path(file).read_bytes()).hexdigest()!=want:sys.exit(1)
 else: print(hashlib.sha256(pathlib.Path(args[0]).read_bytes()).hexdigest()+'  '+args[0])
elif name=='systemctl':pass
elif name=='date':print(os.environ.get('FAKE_NOW','1794400000'))
elif name=='timeout':
 p=results/'timeouts.json'
 seen=json.loads(p.read_text()) if p.exists() else []
 p.write_text(json.dumps(seen+[args[2]]))
 os.execvp(args[3],args[3:])
elif name=='nvidia-smi':
 print('NVIDIA A10G, simulated, 23028 MiB')
 print('GPU query receipt',file=sys.stderr)
 sys.exit(int(os.environ.get('FAKE_GPU_EXIT','0')))
elif name=='docker':
 if args[0]=='pull':
  print('image pull receipt')
  sys.exit(int(os.environ.get('FAKE_PULL_EXIT','0')))
 elif args[0]=='run':
  (results/'invocation.json').write_text(json.dumps(args))
  (results/'result.json').write_text(json.dumps({'status':'passed','simulation':True}))
 elif args[0]=='rm':print('container cleanup attempted')
else:raise RuntimeError(name)
'''


class HostReceiptTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.bundle = self.root / 'bundle'
        self.bundle.mkdir()
        self.results = self.root / 'results'
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        for name in ('docker', 'systemctl', 'date', 'timeout', 'nvidia-smi', 'sha256sum'):
            p = self.bin / name
            p.write_text('#!' + sys.executable + '\n' + FAKE)
            p.chmod(0o755)
        (self.bin / 'python3').symlink_to(sys.executable)
        marker = self.root / 'armed'
        marker.touch()
        for name in ('grind-ranked', 'grind-upstream'):
            p = self.bundle / name
            p.write_text('simulated binary')
            p.chmod(0o555)
        sums = ''.join(hashlib.sha256((self.bundle / name).read_bytes()).hexdigest() + '  ' + name + '\n'
                       for name in ('grind-ranked', 'grind-upstream'))
        (self.bundle / 'SHA256SUMS').write_text(sums)
        self.digest = hashlib.sha256(sums.encode()).hexdigest()
        source = (ROOT / 'ops/aws-gpu-execution/host-pqb-measure.sh').read_text()
        source = source.replace('/opt/qsb-pqb-measure', str(self.bundle)).replace(
            '/var/tmp/qsb-pqb-measure-results', str(self.results)).replace('/run/qsb-shutdown-armed', str(marker))
        self.script = self.root / 'host.sh'
        self.script.write_text(source)

    def tearDown(self):
        self.temp.cleanup()

    def run_host(self, profile='measure', **env):
        return subprocess.run(['bash', str(self.script), str(self.bundle), str(self.results),
                               '1794401000', self.digest, profile], capture_output=True, text=True,
                              env=dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ['PATH'],
                                       FAKE_RESULTS=str(self.results), **env), timeout=30)

    def check_receipt(self, done, code):
        self.assertEqual(done.returncode, code, done.stdout + done.stderr)
        self.assertEqual((self.results / 'exit-code.txt').read_text(), str(code) + '\n')
        raw = (self.results / 'public-result.b64').read_bytes()
        meta = json.loads(next(line.split('=', 1)[1] for line in done.stdout.splitlines()
                               if line.startswith('QSB_PUBLIC_RESULT_META=')))
        self.assertEqual(meta, {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()})
        files = json.loads(gzip.decompress(base64.b64decode(raw, validate=True)))
        self.assertEqual(files['exit-code.txt'], str(code) + '\n')
        self.assertIn('container cleanup attempted', files['container-cleanup.log'])
        return files

    def test_pull_failure_has_a_durable_receipt_and_does_not_run_compute(self):
        files = self.check_receipt(self.run_host(FAKE_PULL_EXIT='73'), 73)
        self.assertIn('image pull receipt', files['image-pull.log'])
        self.assertNotIn('invocation.json', files)
        original = (self.results / 'public-result.b64').read_bytes()
        self.assertNotEqual(self.run_host().returncode, 0)
        self.assertEqual((self.results / 'public-result.b64').read_bytes(), original)

    def test_insufficient_time_has_a_durable_receipt(self):
        files = self.check_receipt(self.run_host(FAKE_NOW='1794400990'), 1)
        self.assertIn('Insufficient time', files['setup-error.txt'])
        self.assertNotIn('invocation.json', files)

    def test_gpu_query_failure_has_a_durable_receipt(self):
        files = self.check_receipt(self.run_host(FAKE_GPU_EXIT='43'), 43)
        self.assertIn('GPU query receipt', files['gpu-error.txt'])
        self.assertNotIn('invocation.json', files)

    def test_correctness_profile_is_short_and_explicit(self):
        files = self.check_receipt(self.run_host('correctness'), 0)
        args = json.loads(files['invocation.json'])
        self.assertIn('--correctness-only', args)
        self.assertIn('QSB_MEASURE_DEADLINE=120', args)
        self.assertEqual(json.loads(files['timeouts.json']), ['300', '180'])
        self.assertEqual(files['profile.txt'], 'correctness\n')

    def test_default_profile_keeps_timing_and_its_original_bound(self):
        files = self.check_receipt(self.run_host(), 0)
        self.assertNotIn('--correctness-only', json.loads(files['invocation.json']))
        self.assertEqual(json.loads(files['timeouts.json']), ['300', '720'])
