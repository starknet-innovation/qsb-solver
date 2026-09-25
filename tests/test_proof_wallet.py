import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('prepare_wallet',ROOT/'ops/fresh-proof/prepare_wallet.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class WalletPreparationTests(unittest.TestCase):
    def test_nested_segwit_known_public_key(self):
        # secp256k1 generator; public test vector, no generated wallet key.
        pub=bytes.fromhex('0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798')
        self.assertEqual(m.nested_address(pub),'3JvL6Ymt8MVWiCNHC7oWU6nLeHNJKLZGLN')
    def test_exclusive_private_permissions(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'private.json';m.save_private(path,{'dummy':'public'})
            self.assertEqual(stat.S_IMODE(path.stat().st_mode),0o600)
            with self.assertRaises(FileExistsError):m.save_private(path,{'changed':True})
            self.assertEqual(json.loads(path.read_text()),{'dummy':'public'})
    def test_wrong_reference_rejected_before_directory_creation(self):
        with tempfile.TemporaryDirectory() as d:
            source=Path(d)/'source';source.mkdir();out=Path(d)/'wallet'
            for name in m.SOURCE_HASHES:(source/name).write_text('untrusted')
            with self.assertRaises(ValueError):m.prepare(source,out)
            self.assertFalse(out.exists())
