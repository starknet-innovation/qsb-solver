import hashlib
import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('historical_handler', ROOT / 'worker/handler.py')
sys.path.insert(0, str(ROOT / 'worker'))
historical = importlib.util.module_from_spec(spec)
spec.loader.exec_module(historical)
sys.modules['historical_handler'] = historical
spec = importlib.util.spec_from_file_location('combined_handler', ROOT / 'worker/promotion/handler.py')
combined = importlib.util.module_from_spec(spec)
spec.loader.exec_module(combined)


class PromotionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        for name in combined.REQUIRED:
            (self.root / name).write_bytes(('public-test-' + name).encode())
        self.binding = {'format': 'qsb-combined-candidate-v1', 'status': 'HOLD',
                        'solverCommit': 'a' * 40,
                        'files': {name: hashlib.sha256((self.root / name).read_bytes()).hexdigest()
                                  for name in combined.REQUIRED}}
        self.save()

    def save(self):
        (self.root / 'pipeline.json').write_text(json.dumps(self.binding))

    def test_exact_artifacts(self):
        self.assertEqual(combined.release_binding(self.root), self.binding)
        for name in combined.REQUIRED:
            original = (self.root / name).read_bytes()
            (self.root / name).write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'artifact mismatch'):
                combined.release_binding(self.root)
            (self.root / name).write_bytes(original)

    def test_missing_file_cannot_drop_guard(self):
        del self.binding['files']['subset']
        self.save()
        with self.assertRaisesRegex(ValueError, 'Invalid combined'):
            combined.release_binding(self.root)

    def test_symlink_rejected_even_if_bytes_match(self):
        source = self.root / 'subset'
        source.rename(self.root / 'other')
        source.symlink_to('other')
        with self.assertRaisesRegex(ValueError, 'artifact mismatch'):
            combined.release_binding(self.root)

    def test_no_self_promotion_or_mutable_source(self):
        for key, value in [('status', 'READY'), ('solverCommit', 'main')]:
            old = self.binding[key]
            self.binding[key] = value
            self.save()
            with self.assertRaisesRegex(ValueError, 'Invalid combined'):
                combined.release_binding(self.root)
            self.binding[key] = old

    def test_wire_identity_and_all_stages_delegated(self):
        with patch.object(combined, 'release_binding', return_value=self.binding), \
                patch.object(historical, 'handler', return_value={'status': 'failed'}) as run:
            for stage in ('pinning', 'round1', 'round2'):
                event = {'input': {'stage': stage}}
                self.assertEqual(combined.handler(event), {'status': 'failed'})
                run.assert_called_with(event)
                self.assertEqual(historical.PINNED_KERNEL, self.binding['solverCommit'])
