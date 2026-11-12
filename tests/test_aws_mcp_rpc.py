"""Durable controller handoff, without an AWS call or credentials."""
import importlib.util
import json
from pathlib import Path
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('qsb_mcp_rpc', ROOT / 'ops/aws-gpu-execution/mcp_rpc.py')
rpc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rpc)


class RpcTest(unittest.TestCase):
    def test_round_trip_and_durable_intent(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = []
            def controller():
                result.append(rpc.exchange(tmp, 'eu-west-1', 'ec2', 'run-instances', {'ClientToken': 'one-shot'}))
            thread = threading.Thread(target=controller)
            thread.start()
            limit = time.monotonic() + 5
            while not list(Path(tmp).glob('*.request.json')) and time.monotonic() < limit:
                time.sleep(0.01)
            path, = Path(tmp).glob('*.request.json')
            request = json.loads(path.read_text())
            self.assertEqual((request['operation'], request['params']), ('RunInstances', {'ClientToken': 'one-shot'}))
            (Path(tmp) / (request['id'] + '.response.json')).write_text(json.dumps({'result': {'Instances': []}}))
            thread.join(5)
            self.assertFalse(thread.is_alive())
            self.assertEqual(result, [{'Instances': []}])
            self.assertTrue(path.exists())

    def test_timeout_preserves_one_uncertain_request_without_retry(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(TimeoutError, 'Uncertain MCP handoff'):
                rpc.exchange(tmp, 'eu-west-1', 'ec2', 'run-instances', {'ClientToken': 'uncertain'}, timeout=0)
            self.assertEqual(len(list(Path(tmp).glob('*.request.json'))), 1)

    def test_receipts_cannot_enter_a_checkout(self):
        with self.assertRaisesRegex(ValueError, 'outside Git'):
            rpc.exchange(ROOT / 'not-created', 'eu-west-1', 'sts', 'get-caller-identity', {})
        self.assertFalse((ROOT / 'not-created').exists())
