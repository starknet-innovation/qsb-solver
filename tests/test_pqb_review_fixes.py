"""Review fixes in the PQB operations code: no AWS call, credentials or Docker."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class LambdaListingTest(unittest.TestCase):
    def setUp(self):
        sys.path.insert(0, str(ROOT / 'ops/pqb-public-solve'))
        self.addCleanup(sys.path.remove, str(ROOT / 'ops/pqb-public-solve'))
        self.control = load('pqb_public_solve_control', 'ops/pqb-public-solve/control.py')

    def pages(self, target_page):
        calls = []

        def call(service, operation, **params):
            calls.append(params)
            page = int(params.get('Marker', '0'))
            names = ['other-%d-%d' % (page, i) for i in range(50)]
            if page == target_page:
                names[7] = 'qsb-pqb-solve-0123abcd'
            return {'Functions': [{'FunctionName': n} for n in names], **({'NextMarker': str(page + 1)} if page < 2 else {})}
        return call, calls

    def test_a_function_beyond_the_first_page_is_found(self):
        call, calls = self.pages(2)
        self.assertTrue(self.control.function_exists(call, 'qsb-pqb-solve-0123abcd'))
        self.assertEqual(calls, [{}, {'Marker': '1'}, {'Marker': '2'}])

    def test_absent_only_after_every_page(self):
        call, calls = self.pages(99)
        self.assertFalse(self.control.function_exists(call, 'qsb-pqb-solve-0123abcd'))
        self.assertEqual(len(calls), 3)


class DurableRequestTest(unittest.TestCase):
    def test_request_is_flushed_before_it_is_published(self):
        rpc = load('qsb_mcp_rpc_durable', 'ops/aws-gpu-execution/mcp_rpc.py')
        events = []
        real_fsync, real_rename = os.fsync, Path.rename

        def fsync(fd):
            events.append('fsync-dir' if os.path.isdir('/dev/fd/%d' % fd) or _is_dir(fd) else 'fsync-file')
            return real_fsync(fd)

        def rename(self, target):
            events.append('rename')
            return real_rename(self, target)

        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(rpc.os, 'fsync', fsync), \
                mock.patch.object(Path, 'rename', rename):
            with self.assertRaises(TimeoutError):
                rpc.exchange(tmp, 'eu-west-1', 'ec2', 'run-instances', {'ClientToken': 'x'}, timeout=0)
            self.assertEqual(events, ['fsync-file', 'rename', 'fsync-dir'])
            self.assertEqual(len(list(Path(tmp).glob('*.request.json'))), 1)
            self.assertEqual(list(Path(tmp).glob('*.partial')), [])


def _is_dir(fd):
    import stat
    return stat.S_ISDIR(os.fstat(fd).st_mode)


class PublisherFailureTest(unittest.TestCase):
    def setUp(self):
        # the publisher imports boto3 lazily; these stand-ins are never called before the failure
        for name in ('boto3', 'botocore', 'botocore.config'):
            if name not in sys.modules:
                sys.modules[name] = types.ModuleType(name)
                self.addCleanup(sys.modules.pop, name)
        if not hasattr(sys.modules['botocore.config'], 'Config'):
            sys.modules['botocore.config'].Config = lambda **options: options
        self.publisher = load('pqb_publish_private', 'ops/pqb-public-solve/publish_private.py')
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.artifact = Path(self.tmp.name) / 'artifact'
        self.artifact.mkdir()
        for name in ('image.tar.gz', 'image.json', 'binding.json', 'source-commit'):
            (self.artifact / name).write_text(name)
        self.repository = '123456789012.dkr.ecr.eu-west-1.amazonaws.com/qsb-pqb-solve-0123abcd'

    def sums(self, **wrong):
        (self.artifact / 'SHA256SUMS').write_text(''.join(
            '%s  %s\n' % (wrong.get(n, hashlib.sha256((self.artifact / n).read_bytes()).hexdigest()), n)
            for n in ('image.tar.gz', 'image.json', 'binding.json', 'source-commit')))

    def test_a_failure_after_the_marker_leaves_a_terminal_receipt(self):
        self.sums(**{'image.json': '0' * 64})
        output = Path(self.tmp.name) / 'receipt.json'
        with self.assertRaisesRegex(ValueError, 'Artifact hash mismatch'):
            self.publisher.publish(self.artifact, self.repository, 'eu-west-1', output)
        receipt = json.loads(output.read_text())
        self.assertEqual((receipt['status'], receipt['stage'], receipt['registryStateUncertain']),
                         ('failed', 'verifying the artifact', False))
        self.assertIn('Artifact hash mismatch: image.json', receipt['error'])
        with self.assertRaisesRegex(ValueError, 'already exists'):          # still one-shot
            self.publisher.publish(self.artifact, self.repository, 'eu-west-1', output)

    def test_a_failure_after_the_push_started_is_marked_uncertain(self):
        self.sums()
        (self.artifact / 'image.json').write_text(json.dumps([{'Id': 'sha256:abc'}]))
        binding = {'solverCommit': 'source-commit', 'status': 'HOLD', 'cudaArchitecture': '86'}
        (self.artifact / 'binding.json').write_text(json.dumps(binding))
        self.sums()
        output = Path(self.tmp.name) / 'receipt.json'

        def run(command, **kwargs):
            if command[:2] == ['docker', 'push']:
                raise RuntimeError('connection reset during push')
            return mock.Mock(returncode=0)

        def check_output(command, **kwargs):
            return 'sha256:abc\n' if 'inspect' in command else json.dumps(binding)

        client = mock.Mock()
        client.get_authorization_token.return_value = {'authorizationData': [{'authorizationToken': 'dTpw'}]}
        # patched, not assigned: a real installed boto3 keeps its own client afterwards
        with mock.patch.object(sys.modules['boto3'], 'client', lambda *a, **k: client, create=True), \
                mock.patch.object(self.publisher.subprocess, 'run', run), \
                mock.patch.object(self.publisher.subprocess, 'check_output', check_output):
            with self.assertRaisesRegex(RuntimeError, 'connection reset'):
                self.publisher.publish(self.artifact, self.repository, 'eu-west-1', output)
        receipt = json.loads(output.read_text())
        self.assertEqual((receipt['status'], receipt['stage'], receipt['registryStateUncertain']),
                         ('failed', 'pushing', True))


if __name__ == '__main__':
    unittest.main()
