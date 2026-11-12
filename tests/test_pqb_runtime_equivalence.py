import copy
import gzip
import json
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from compare_pqb_runtime import compare_tables,ca_only_delta


class RuntimeEquivalenceTests(unittest.TestCase):
    def tables(self):
        root=ROOT/'docs/pqb/evidence/tls-replacement-2026-11-12/equivalence'
        return tuple(json.loads(gzip.decompress((root/name).read_bytes())) for name in
                     ('reference-files.json.gz','candidate-files.json.gz'))

    def test_complete_real_inventory_and_timestamp_cache_payloads(self):
        old,new=self.tables();result=compare_tables(old,new)
        self.assertEqual(result['files'],11044)
        self.assertEqual(len(result['changes']),203)
        self.assertEqual(len(result['pythonCacheTimestampPaths']),195)

    def test_changed_compute_loader_permissions_or_inventory_fail(self):
        old,new=self.tables()
        for path in ('opt/qsb-pqb/grind','opt/qsb-pqb/pqb_handler.py','etc/ld.so.cache'):
            changed=copy.deepcopy(new);changed[path]['sha256']='0'*64
            with self.subTest(path=path),self.assertRaises(ValueError):compare_tables(old,changed)
        changed=copy.deepcopy(new);changed['opt/qsb-pqb/grind']['mode']=0o777
        with self.assertRaises(ValueError):compare_tables(old,changed)
        changed=copy.deepcopy(new);changed['unexpected-file']=copy.deepcopy(new['opt/qsb-pqb/grind'])
        with self.assertRaises(ValueError):compare_tables(old,changed)

    def test_cache_code_and_source_cannot_hide_behind_timestamp_normalization(self):
        old,new=self.tables()
        path=next(p for p in new if p.endswith('.pyc') and old[p]['sha256']!=new[p]['sha256'])
        for field,value in [('pycCodeSha256','0'*64),('pycHeader','00'*16)]:
            changed=copy.deepcopy(new);changed[path][field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):compare_tables(old,changed)

    def test_only_reviewed_ca_keyword_can_change_transport_semantics(self):
        old=b"client = boto3.client('s3', config=Config(connect_timeout=5, read_timeout=15))"
        new=old.replace(b"config=",b"verify='/etc/ssl/certs/ca-certificates.crt', config=")
        ca_only_delta(old,new)
        for changed in (new.replace(b'read_timeout=15',b'read_timeout=99'),
                        new.replace(b"verify='/etc/ssl/certs/ca-certificates.crt'",b'verify=False'),old):
            with self.assertRaises(ValueError):ca_only_delta(old,changed)
