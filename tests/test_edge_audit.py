import hashlib,importlib.util,json,unittest
from pathlib import Path
ROOT=Path(__file__).parents[1]
spec=importlib.util.spec_from_file_location('edge',ROOT/'worker/promotion/validation/build_edge_audit.py')
edge=importlib.util.module_from_spec(spec);spec.loader.exec_module(edge)

class EdgeAudit(unittest.TestCase):
    def setUp(self):
        self.source=ROOT/'research/optimized-subset'
        self.tree=(self.source/'subset/tests/gpu_epochs/tree.cu').read_text()
        self.resolve=(self.source/'subset/tests/gpu_epochs/exact_resolve.cuh').read_text()
    def test_capacity_keeps_fail_closed_host_guard(self):
        result=edge.capacity_source(self.tree)
        self.assertIn('if (h_hit > 64)',result)
        self.assertLess(result.index('DEVICE_COUNT'),result.index('if (h_hit > 64)'))
        self.assertIn('if(p<1024)',result)
        self.assertIn('CANARY_CORRUPT',result)
    def test_forced_and_detector_paths_are_distinct(self):
        forced,resolver=edge.exception_source(self.tree,self.resolve,True)
        detected,_=edge.exception_source(self.tree,self.resolve,False)
        self.assertIn('bool usable = false;',forced)
        self.assertIn('bool usable = active &&',detected)
        self.assertIn('accept=false;',resolver)
        self.assertIn('qsb_exact_der',resolver)
    def test_original_inventory_stays_locked(self):
        lock=json.loads((ROOT/'worker/optimized/source-lock.json').read_text())
        actual={str(p.relative_to(self.source)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (self.source/'subset').rglob('*') if p.is_file()}
        self.assertEqual(actual,lock['files'])
    def test_anchor_drift_rejected(self):
        with self.assertRaises(ValueError):edge.capacity_source('')
        with self.assertRaises(ValueError):edge.exception_source('',self.resolve,True)
