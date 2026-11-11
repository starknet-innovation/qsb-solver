"""The native measurement run's bundle and runner, dry-run on CPU-emulated binaries.

This proves the run's mechanics and result collection before any paid hardware. The rates it
produces are emulation rates and mean nothing about a GPU.
"""
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
import pqb_emulation as emu  # noqa: E402

MEASURE = ROOT / 'research/pqb-ranked/measure'
RANKED = emu.build()
UPSTREAM = emu.build(emu.UPSTREAM)
COMMIT = 'ef' * 20
FAST = {'QSB_MEASURE_SAMPLES': '1', 'QSB_MEASURE_SECONDS': '2', 'QSB_MEASURE_STRATA': '2'}


def bundle_module():
    spec = importlib.util.spec_from_file_location('prepare_pqb_measure_bundle', ROOT / 'scripts/prepare_pqb_measure_bundle.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class ExpectedTest(unittest.TestCase):
    def test_expected_binds_the_committed_fixtures(self):
        expected = json.loads((MEASURE / 'expected.json').read_text())
        self.assertEqual({f.name for f in emu.FIXTURES.glob('*.txt')}, set(expected['fixtures']))
        for name, digest in expected['fixtures'].items():
            self.assertEqual(sha256(emu.FIXTURES / name), digest, name)
        labels = [c['label'] for c in expected['cases']]
        self.assertEqual(len(labels), len(set(labels)))
        self.assertIn('pin-planted-exceptional', labels)
        self.assertGreater(sum(len(c['hits']) for c in expected['cases']), 200)

    def test_host_script_uses_the_published_runtime_and_isolates_the_run(self):
        text = (ROOT / 'ops/aws-gpu-execution/host-pqb-measure.sh').read_text()
        status = (ROOT / 'docs/README.md').read_text()
        digest = 'sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48'
        self.assertIn(digest, text)
        self.assertIn(digest, status)
        for flag in ('--network none', '--read-only', '--cap-drop ALL', 'no-new-privileges', 'sha256sum -c SHA256SUMS'):
            self.assertIn(flag, text)


@unittest.skipUnless(RANKED and UPSTREAM, 'no C++ compiler')
class MeasureDryRunTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.artifact = root / 'artifact'
        self.artifact.mkdir()
        shutil.copy(RANKED, self.artifact / 'grind-ranked')
        shutil.copy(UPSTREAM, self.artifact / 'grind-upstream')
        lock = json.loads((ROOT / 'research/pqb-ranked/source-lock.json').read_text())
        (self.artifact / 'build-receipt.json').write_text(json.dumps(
            {'status': 'HOLD', 'binarySha256': sha256(self.artifact / 'grind-ranked'), 'sourceLock': lock}))
        (self.artifact / 'source-commit').write_text(COMMIT + '\n')
        self.sums()
        self.bundle = root / 'bundle'

    def tearDown(self):
        self.tmp.cleanup()

    def sums(self):
        (self.artifact / 'SHA256SUMS').write_text(''.join(
            '%s  %s\n' % (sha256(self.artifact / n), n) for n in ('grind-ranked', 'grind-upstream', 'build-receipt.json')))

    def runner(self, result):
        return subprocess.run([sys.executable, str(self.bundle / 'run_measure.py'), str(self.bundle), str(result)],
                              capture_output=True, text=True, env=dict(os.environ, **FAST), timeout=600)

    def test_bundle_and_one_shot_run(self):
        digest = bundle_module().prepare(self.artifact, self.bundle, commit=COMMIT)
        self.assertEqual(digest, sha256(self.bundle / 'SHA256SUMS'))
        done = subprocess.run(['shasum', '-a', '256', '-c', 'SHA256SUMS'], cwd=self.bundle, capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        result = Path(self.tmp.name) / 'result.json'
        done = self.runner(result)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        out = json.loads(result.read_text())
        self.assertEqual((out['status'], out['correctnessPassed']), ('passed', True))
        self.assertEqual(out['binaries']['grind-ranked'], sha256(self.artifact / 'grind-ranked'))
        self.assertEqual(len(out['correctness']), 11)
        for stage in ('pin', 'round0', 'round1'):
            summary = out['timing'][stage]['summary']
            self.assertGreater(summary['rankedOverUpstreamSteady'], 0)
            modes = [s['mode'] for s in out['timing'][stage]['samples']]
            self.assertEqual(modes, ['upstream-random', 'ranked'])           # interleaved
        again = self.runner(result)                                           # one-shot
        self.assertNotEqual(again.returncode, 0)
        self.assertEqual(json.loads(result.read_text())['status'], 'passed')

    def test_a_wrong_answer_fails_the_run_and_is_not_timed(self):
        bundle_module().prepare(self.artifact, self.bundle, commit=COMMIT)
        expected = json.loads((self.bundle / 'expected.json').read_text())
        expected['cases'] = expected['cases'][:2]
        expected['cases'][1]['hits'] = expected['cases'][1]['hits'][1:]       # the grinder finds one more
        (self.bundle / 'expected.json').write_text(json.dumps(expected))
        result = Path(self.tmp.name) / 'result.json'
        done = self.runner(result)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        out = json.loads(result.read_text())
        self.assertEqual((out['status'], out['timing']), ('failed', None))
        self.assertEqual([c['pass'] for c in out['correctness']], [True, False])

    def test_bundle_refuses_mismatched_inputs(self):
        prepare = bundle_module().prepare
        with self.assertRaises(SystemExit):
            prepare(self.artifact, self.bundle, commit='00' * 20)             # built from another commit
        with open(self.artifact / 'grind-upstream', 'ab') as f:
            f.write(b'\0')
        with self.assertRaises(SystemExit):
            prepare(self.artifact, self.bundle, commit=COMMIT)                # differs from its sums
        self.sums()
        receipt = json.loads((self.artifact / 'build-receipt.json').read_text())
        receipt['sourceLock'] = dict(receipt['sourceLock'], status='OTHER')
        (self.artifact / 'build-receipt.json').write_text(json.dumps(receipt))
        self.sums()
        with self.assertRaises(SystemExit):
            prepare(self.artifact, self.bundle, commit=COMMIT)                # another source lock


if __name__ == '__main__':
    unittest.main()
