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

    def test_checkout_destination_rejected_before_source_access(self):
        with self.assertRaisesRegex(ValueError, 'outside the source checkout'):
            m.prepare('/does-not-exist', ROOT/'new-wallet-must-not-exist')
        self.assertFalse((ROOT/'new-wallet-must-not-exist').exists())

    def test_other_checkout_and_worktree_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            (root/'.git').write_text('gitdir: /dummy/public/test')
            with self.assertRaisesRegex(ValueError, 'every Git checkout'):
                m.validate_destination(root/'nested'/'wallet')

    def test_symlink_into_checkout_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            link=Path(d)/'alias';link.symlink_to(ROOT, target_is_directory=True)
            with self.assertRaises(ValueError):m.validate_destination(link/'new-wallet')

    def test_external_destination_allowed_without_writes(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'new-wallet'
            self.assertEqual(m.validate_destination(path), path.resolve())
            self.assertFalse(path.exists())
