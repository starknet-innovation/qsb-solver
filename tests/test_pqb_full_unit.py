"""Full-unit harness mechanics on public CPU emulation; never GPU timing evidence."""
import hashlib
import importlib.util
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'worker/pqb'))
import pqb_emulation as emu
import pqb_handler as worker
import pqb_ranges as ranges
import prepare_pqb_full_unit_bundle as packaging

runner = packaging.module('full_unit_test_runner', ROOT / 'research/pqb-ranked/measure/run_full_unit.py')
reference = packaging.module('full_unit_test_reference', ROOT / 'research/pqb-ranked/tests/reference.py')
COMMIT = 'ac' * 20
BINARY = emu.build()


@unittest.skipUnless(BINARY, 'no C++ compiler')
class FullUnitTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        artifact = self.root / 'artifact'
        artifact.mkdir()
        for name in ('grind-ranked', 'grind-upstream'):
            shutil.copy(BINARY, artifact / name)
        lock = json.loads((ROOT / 'research/pqb-ranked/source-lock.json').read_text())
        (artifact / 'build-receipt.json').write_text(json.dumps(
            {'format': 'qsb-pqb-build-receipt-v1', 'cudaArchitecture': '86', 'status': 'HOLD',
             'binarySha256': runner.sha256(BINARY), 'sourceLock': lock}))
        (artifact / 'source-commit').write_text(COMMIT + '\n')
        (artifact / 'source-event').write_text('push\n')
        (artifact / 'SHA256SUMS').write_text(''.join('%s  %s\n' % (runner.sha256(artifact / name), name)
            for name in ('grind-ranked', 'grind-upstream', 'build-receipt.json')))
        self.artifact = artifact
        self.bundle = self.root / 'bundle'
        self.git = {('rev-parse', 'HEAD'): COMMIT, ('status', '--porcelain'): '',
                    ('ls-remote', '--heads', 'origin'): COMMIT + '\trefs/heads/test'}
        with patch.object(packaging.measurement, 'git', side_effect=lambda *args: self.git[args]):
            self.digest = packaging.prepare(artifact, self.bundle)
        self.results = self.root / 'results'

    def tearDown(self):
        self.temp.cleanup()

    def test_bundle_and_largest_plan_bind_actual_inputs(self):
        runner.verify_bundle(self.bundle)
        self.assertEqual(self.digest, runner.sha256(self.bundle / 'SHA256SUMS'))
        plan = json.loads((self.bundle / 'plan.json').read_text())
        self.assertEqual(plan, {'searchVersion': 'pqb-ranked-v2', 'attempts': {stage: 0 for stage in runner.STAGES}})
        for stage in ('round0', 'round1'):
            maximum = ranges.work_range(stage, plan['attempts'][stage])['count']
            self.assertTrue(all(ranges.work_range(stage, i)['count'] <= maximum for i in range(ranges.unit_count(stage))))
        with open(self.bundle / 'fixtures/pin.txt', 'ab') as file:
            file.write(b'x')
        with self.assertRaisesRegex(ValueError, 'bundle input mismatch'):
            runner.verify_bundle(self.bundle)

    def test_packaging_requires_clean_pushed_exact_source(self):
        for changed in ({('status', '--porcelain'): ' M file'},
                        {('ls-remote', '--heads', 'origin'): '00' * 20 + '\trefs/heads/test'},
                        {('rev-parse', 'HEAD'): '00' * 20}):
            git = dict(self.git, **{})
            git.update(changed)
            with patch.object(packaging.measurement, 'git', side_effect=lambda *args: git[args]), self.assertRaises(SystemExit):
                packaging.prepare(self.artifact, self.root / 'refused')

    def small_unit(self, stage):
        if stage == 'pinning':
            return {'version': ranges.VERSION, 'start': '0', 'count': 400, 'sequence': ranges.SEQ_MIN,
                    'sequenceCount': 2, 'locktime': ranges.LT_MIN, 'locktimeCount': 200}
        first = ranges.subset_rank_of_prefix(stage, 5)
        return {'version': ranges.VERSION, 'start': str(first),
                'count': ranges.subset_rank_of_prefix(stage, 8) - first, 'prefixStart': '5', 'prefixCount': 3}

    def test_real_handler_retains_receipts_for_each_stage(self):
        for stage in runner.STAGES:
            results = self.root / stage
            results.mkdir()
            with patch.object(worker, 'work_range', return_value=self.small_unit(stage)):
                row = runner.run_case(self.bundle, results, stage, 0, worker, reference)
            self.assertTrue(row['pass'], row)
            self.assertFalse(row['nativeDevice'])        # emulation can never certify native execution
            self.assertEqual(row['batchZblocks'], self.small_unit(stage)['count'])
            self.assertTrue((results / 'work/compute.log').is_file())
            self.assertTrue((results / 'work/hits.txt').is_file())
            self.assertEqual(json.loads((results / 'worker-result.json').read_text())['status'], 'completed')
            # Reusing the evidence directory refuses to run again.
            before = (results / 'work/compute.log').read_bytes()
            with self.assertRaises(FileExistsError), patch.object(worker, 'work_range', return_value=self.small_unit(stage)):
                runner.run_case(self.bundle, results, stage, 0, worker, reference)
            self.assertEqual((results / 'work/compute.log').read_bytes(), before)

    def test_timeout_and_bad_accounting_are_uncredited_and_durable(self):
        actual = worker.handler
        self.results.mkdir()
        with patch.object(worker, 'handler', side_effect=lambda *args, **kw: actual(*args, timeout=0.001, **kw)):
            row = runner.run_case(self.bundle, self.results, 'pinning', 0, worker, reference)
        self.assertFalse(row['pass'])
        self.assertEqual(row['workerResult']['status'], 'interrupted')
        self.assertTrue((self.results / 'work/compute.log').exists())
        bad = dict(self.small_unit('pinning'), count=401)
        results = self.root / 'bad-accounting'
        results.mkdir()
        with patch.object(worker, 'work_range', return_value=bad):
            row = runner.run_case(self.bundle, results, 'pinning', 0, worker, reference)
        self.assertFalse(row['pass'])
        self.assertEqual(row['workerResult']['status'], 'failed')
        self.assertIn('@range ', (results / 'work/compute.log').read_text())

    def test_bad_preflight_prevents_full_unit_and_results_are_one_shot(self):
        sys.path.insert(0, str(ROOT / 'research/pqb-ranked/measure'))
        import run_measure
        with patch.object(run_measure, 'correctness', return_value=[{'pass': False}]), patch.object(worker, 'handler') as launch:
            result = runner.run(self.bundle, self.results, 'round0')
        self.assertEqual(result['status'], 'failed')
        self.assertIn('small-range correctness preflight failed', result['error'])
        launch.assert_not_called()
        original = (self.results / 'result.json').read_bytes()
        with self.assertRaises(FileExistsError):
            runner.run(self.bundle, self.results, 'round0')
        self.assertEqual((self.results / 'result.json').read_bytes(), original)

    def test_overrides_and_tampering_fail_before_compute(self):
        with patch.dict(os.environ, {'QG_TEST_ALL_EXCEPTIONAL': '1'}):
            out = runner.run(self.bundle, self.results, 'pinning')
        self.assertIn('overrides', out['error'])
        (self.bundle / 'worker/grind').chmod(0o755)
        (self.bundle / 'worker/grind').write_bytes(b'corrupt')
        out = runner.run(self.bundle, self.root / 'tampered', 'pinning')
        self.assertIn('bundle input mismatch', out['error'])

    def test_candidate_membership_selectors_and_gate_are_independent(self):
        prob = reference.load(self.bundle / 'fixtures/pin.txt')
        unit = self.small_unit('pinning')
        good = '%d %d 0 0 0 1' % (unit['sequence'], unit['locktime'])
        shaped = bytes.fromhex('301d0201') + b'\x01\x02\x18' + bytes(25)
        with patch.object(reference, 'pin_digest', return_value=shaped):
            checked = runner.verify_candidate(reference, prob, 'pinning', unit, good)
        self.assertEqual(checked['nonce'], '0')
        bad = [good.replace('0 0 0 1', '12 0 0 1'), good.replace('0 0 0 1', '0 0 3 1'),
               '%d %d 0 0 0 1' % (unit['sequence'] + 3, unit['locktime'])]
        for line in bad:
            with self.assertRaises(ValueError):
                runner.verify_candidate(reference, prob, 'pinning', unit, line)
        with self.assertRaisesRegex(ValueError, 'gate or DER'):
            runner.verify_candidate(reference, prob, 'pinning', unit, good)


if __name__ == '__main__':
    unittest.main()
