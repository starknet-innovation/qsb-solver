"""Wire fences before any process creation; opaque parameters still need app verification."""
import base64
import hashlib
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'worker'))
spec = importlib.util.spec_from_file_location('script_version_handler', ROOT / 'worker/handler.py')
worker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(worker)


class ScriptVersionTests(unittest.TestCase):
    def request(self, stage='round1'):
        raw = b'public synthetic bytes' * 4
        return dict(protocol='qsb-config-a-v1', stage=stage,
                    parameterBase64=base64.b64encode(raw).decode(),
                    parameterSha256=hashlib.sha256(raw).hexdigest(), manifestHash='a'*64,
                    kernelCommit=worker.PINNED_KERNEL, searchVersion='ranked-v2', attempt=0,
                    sequence=2147483648, locktime=500000000)

    def test_legacy_wire_stays_legacy(self):
        worker.validate_request(self.request())
        worker.validate_request(dict(self.request(), scriptVersion=worker.LEGACY_SCRIPT_VERSION))
        with self.assertRaises(ValueError):
            worker.validate_request(dict(self.request(), scriptVersion=worker.CORRECTED_SCRIPT_VERSION))

    def test_corrected_all_stages_require_explicit_binding_before_compute(self):
        for stage in ('pinning', 'round1', 'round2'):
            request = self.request(stage)
            worker.validate_request(dict(request, scriptVersion=worker.CORRECTED_SCRIPT_VERSION), worker.CORRECTED_SCRIPT_VERSION)
            for value in (None, worker.LEGACY_SCRIPT_VERSION, 'unknown', [], 1):
                data = request if value is None else dict(request, scriptVersion=value)
                with patch.object(worker.subprocess, 'Popen') as process:
                    with self.assertRaises(ValueError):
                        worker.handler({'input': data}, worker.CORRECTED_SCRIPT_VERSION)
                    process.assert_not_called()

    def test_corrected_failed_compute_echoes_binding_without_credit(self):
        data = dict(self.request(), scriptVersion=worker.CORRECTED_SCRIPT_VERSION)
        with patch.object(worker.subprocess, 'Popen') as process:
            process.return_value.returncode = 2
            result = worker.handler({'input': data}, worker.CORRECTED_SCRIPT_VERSION)
        self.assertEqual(result['scriptVersion'], worker.CORRECTED_SCRIPT_VERSION)
        self.assertEqual(result['status'], 'failed')
        self.assertNotEqual(result['checkpoint'], 'range-complete')
        self.assertFalse(result['verified'])

    def test_unknown_installed_version_refused(self):
        with self.assertRaises(ValueError): worker.validate_request(self.request(), 'unknown')
