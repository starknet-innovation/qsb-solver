import base64
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
def load(name, path):
    spec=importlib.util.spec_from_file_location(name, ROOT/path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module
m=load('proof_results','ops/fresh-proof/results.py')
r=load('fresh_sm86','worker/promotion/validation/run_fresh_sm86.py')
s=load('ranges','worker/search_ranges.py')

class ResultsTests(unittest.TestCase):
    def setUp(self):
        self.batch=dict(batchId='00000000-0000-4000-8000-000000000001',maxAttempts=1,
            request=dict(kernelCommit=r.COMMIT,stage='pinning',attempt=0,manifestHash='a'*64))
        self.raw=json.dumps(self.batch).encode()
        def invoke(event):
            return dict(event['input'],status='completed',checkpoint='range-complete',
                        verified=False,candidates=[],workRange=s.work_range('pinning',0))
        state=r.run_batch(self.batch,invoke,s.work_range,lambda value:None)
        state.update(binding=dict(solverCommit=r.COMMIT,architecture='sm_86',files=dict(pinning=r.PIN,subset=r.SUB)),
                     batchSha256=hashlib.sha256(self.raw).hexdigest())
        self.files=dict(zip(sorted(m.FILES),['']*len(m.FILES)))
        self.files.update({'result.json':json.dumps(state),'exit-code.txt':'0'})
    def encode(self, files=None):
        data=base64.b64encode(gzip.compress(json.dumps(files or self.files).encode()))
        return data,dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    def bind(self, files=None, raw=None):
        return m.bind_result(files or self.files,raw or self.raw,r.validate_batch,r.validate_binding,s.work_range)
    def test_roundtrip_retains_no_credit(self):
        data,meta=self.encode()
        self.assertEqual(m.assemble_chunks([(0,data[:100]),(100,data[100:])],meta),data)
        result=self.bind(m.decode_archive(data,meta))
        self.assertEqual(result['completedWorkerRows'],1)
        self.assertFalse(result['grantsRangeCredit'])
    def test_gaps_overlap_and_corruption(self):
        data,meta=self.encode()
        for chunks in [[(1,data)],[(0,data[:100]),(99,data[100:])],[(0,data[:-1])],[(0,b'x'+data[1:])]]:
            with self.assertRaises(ValueError):m.assemble_chunks(chunks,meta)
    def test_unknown_file_rejected(self):
        data,meta=self.encode(dict(self.files,**{'../wallet.json':'no'}))
        with self.assertRaises(ValueError):m.decode_archive(data,meta)
    def test_wrong_batch_and_binding(self):
        with self.assertRaises(ValueError):self.bind(raw=self.raw+b' ')
        state=json.loads(self.files['result.json']);state['binding']['files']['subset']='0'*64
        with self.assertRaises(ValueError):self.bind(dict(self.files,**{'result.json':json.dumps(state)}))
    def test_skipped_range_or_false_completion(self):
        for change in ['skip','short','exit']:
            files=copy.deepcopy(self.files);state=json.loads(files['result.json'])
            if change=='skip':state['results'][0]['attempt']=1
            elif change=='short':state['results']=[]
            else:files['exit-code.txt']='124'
            files['result.json']=json.dumps(state)
            with self.assertRaises(ValueError):self.bind(files)
    def test_interrupted_result_requires_reconciliation(self):
        state=json.loads(self.files['result.json']);state.update(status='running',activeAttempt=1)
        result=self.bind(dict(self.files,**{'result.json':json.dumps(state),'exit-code.txt':'124'}))
        self.assertTrue(result['requiresReconciliation']);self.assertFalse(result['grantsRangeCredit'])
    def test_decompression_bounded(self):
        data=base64.b64encode(gzip.compress(b' '*(m.MAX_DECODED+1)))
        with self.assertRaises(ValueError):m.decode_archive(data,dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
    def test_duplicate_json_keys_reject(self):
        data=base64.b64encode(gzip.compress(b'{"result.json":"a","result.json":"b"}'))
        with self.assertRaises(ValueError):m.decode_archive(data,dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
    def test_persistence_exclusive_and_hash_bound(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)/'collection';data,meta=self.encode()
            receipt=m.persist_collection(out,data,meta,self.raw,r.validate_batch,r.validate_binding,s.work_range)
            self.assertEqual(receipt['files']['batch.json'],hashlib.sha256(self.raw).hexdigest())
            self.assertTrue((out/'collection-receipt.json').exists())
            with self.assertRaises(FileExistsError):
                m.persist_collection(out,data,meta,self.raw,r.validate_batch,r.validate_binding,s.work_range)
    def test_invalid_collection_creates_no_evidence_directory(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)/'collection';data,meta=self.encode()
            with self.assertRaises(ValueError):
                m.persist_collection(out,data[:-1],meta,self.raw,r.validate_batch,r.validate_binding,s.work_range)
            self.assertFalse(out.exists())

    def test_contradictory_clean_evidence_rejected(self):
        for extra in [dict(failedResult={'status':'failed'}),dict(errorType='TimeoutError'),
                      dict(neverStartedAttempt=-99),dict(neverStartedAttempt=1)]:
            state=json.loads(self.files['result.json']);state.update(extra)
            with self.assertRaises(ValueError):self.bind(dict(self.files,**{'result.json':json.dumps(state)}))
    def test_valid_never_started_bounded_stop(self):
        state=json.loads(self.files['result.json'])
        state.update(status='bounded-stop',results=[],neverStartedAttempt=0)
        result=self.bind(dict(self.files,**{'result.json':json.dumps(state)}))
        self.assertFalse(result['requiresReconciliation'])
        self.assertEqual(result['completedWorkerRows'],0)
    def test_parent_directory_is_synced(self):
        import tempfile
        import os
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)/'collection';data,meta=self.encode()
            with patch('os.open',wraps=os.open) as opened, patch('os.fsync',wraps=os.fsync) as synced:
                m.persist_collection(out,data,meta,self.raw,r.validate_batch,r.validate_binding,s.work_range)
                opened.assert_any_call(out.parent,os.O_RDONLY)
                opened.assert_any_call(out,os.O_RDONLY)
                self.assertGreaterEqual(synced.call_count,10)
