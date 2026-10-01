from pathlib import Path
import hashlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'experiments/generic-sha-vector'))
from prepared_verdict_experiment import check_prepared


class PreparedVerdictTests(unittest.TestCase):
    def test_writable_input_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'public.json'
            p.write_bytes(b'{}')
            with self.assertRaisesRegex(ValueError, 'writable'):
                check_prepared(directory, {p.name: hashlib.sha256(p.read_bytes()).hexdigest()})

    def test_changed_read_only_input_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'public.json'
            p.write_bytes(b'{"changed":true}')
            p.chmod(0o444)
            with self.assertRaisesRegex(ValueError, 'drift'):
                check_prepared(directory, {p.name: hashlib.sha256(b'{}').hexdigest()})

    def test_matching_read_only_input_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'public.json'
            p.write_bytes(b'{}')
            p.chmod(0o444)
            check_prepared(directory, {p.name: hashlib.sha256(b'{}').hexdigest()})
