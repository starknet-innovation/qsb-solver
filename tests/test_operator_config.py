import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.append(str(Path(__file__).resolve().parents[1]/'ops/aws-gpu-execution'))
import operator_config as m

class OperatorConfigTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name)/'operator.json'
        self.value=dict(account='123456789012',profile='test',region='eu-west-1',
                        ami='ami-00000000',subnet='subnet-00000000',vpc='vpc-00000000')
        self.path.write_text(json.dumps(self.value))
        p=patch.dict(os.environ,QSB_AWS_OPERATOR_CONFIG=str(self.path));p.start();self.addCleanup(p.stop)
    def test_exact_external_configuration(self):
        self.assertEqual(m.load_config(),self.value)
    def test_missing_configuration_rejected(self):
        with patch.dict(os.environ,{},clear=True):
            with self.assertRaises(ValueError):m.load_config()
    def test_other_region_unknown_field_and_bad_id_rejected(self):
        for value in (dict(self.value,region='us-east-1'),dict(self.value,token='no'),dict(self.value,account='wrong')):
            self.path.write_text(json.dumps(value))
            with self.assertRaises(ValueError):m.load_config()
    def test_duplicate_key_rejected(self):
        self.path.write_text('{"account":"123456789012","account":"123456789012"}')
        with self.assertRaises(ValueError):m.load_config()
    def test_git_checkout_rejected(self):
        (self.path.parent/'.git').write_text('gitdir: dummy')
        with self.assertRaises(ValueError):m.load_config()
