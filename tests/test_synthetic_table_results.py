import copy
import importlib.util
import unittest
from pathlib import Path
s=importlib.util.spec_from_file_location('synthetic_runner',Path(__file__).resolve().parents[1]/'experiments/synthetic-table-e2e/run.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def report(arm,n):
    return dict(status='passed',schema=1,noSolverSearch=True,arm=arm,repetitions=n,public_scalar=1,geometry=15,records_per_table=1048576,openssl_samples_per_table=252,table_sha256=m.EXPECTED_TABLE,expected_table_sha256=m.EXPECTED_TABLE,original_kernel_sha256=m.KERNEL,gpu='NVIDIA A10G',context_init_ms=1,output_allocation_ms=1,output_cleanup_ms=1,before_report_elapsed_ms=3+n*8,tables=[dict(index=i,table_sha256=m.EXPECTED_TABLE,construction_ms=7,ladder_ms=1,allocate_ms=1,upload_ms=1,kernel_wall_ms=1,download_ms=1,verification_ms=1,cleanup_ms=1,kernel_ms=.5,hash_ms=1) for i in range(n)])
def receipt():
    return dict(status='passed',sanitizers=[dict(tool=t,arm=a,seconds=1,report=report(a,1)) for t in ('memcheck','racecheck','synccheck') for a in ('baseline','candidate')],samples=[dict(repetitions=n,pair=p,arm=a,processSeconds=1,pipelineSeconds=1.01,report=report(a,n)) for n in m.REPETITIONS for p in range(m.PAIRS) for a in (('baseline','candidate') if p%2==0 else ('candidate','baseline'))])
class SyntheticResults(unittest.TestCase):
    def test_complete_fixed_inventory(self):
        v=m.summarize(receipt());self.assertEqual(v['16']['medianRatio'],1)
    def test_prerequisites_and_completeness(self):
        for key in ('samples','sanitizers'):
            r=receipt();r[key].pop()
            with self.assertRaises(ValueError):m.summarize(r)
    def test_invalid_times_and_indices(self):
        for key,value in [('pair',False),('repetitions',True),('processSeconds',0),('pipelineSeconds',float('inf')),('pipelineSeconds',.01)]:
            r=receipt();r['samples'][0][key]=value
            with self.assertRaises(ValueError):m.summarize(r)
    def test_schema_and_arithmetic_identity(self):
        for key,value in [('public_scalar',2),('records_per_table',True),('original_kernel_sha256','0'*64),('table_sha256','0'*64),('tables',[])]:
            r=report('baseline',1);r[key]=value
            with self.assertRaises(ValueError):m.check_report(r,'baseline',1)
    def test_invalid_phase_partition(self):
        r=report('baseline',1);r['tables'][0]['upload_ms']=0
        with self.assertRaises(ValueError):m.check_report(r,'baseline',1)
        r=report('baseline',1);r['before_report_elapsed_ms']=1
        with self.assertRaises(ValueError):m.check_report(r,'baseline',1)
    def test_strict_json(self):
        for raw in ('{"a":1,"a":2}','{"a":NaN}'):
            with self.assertRaises(ValueError):m.strict_json(raw)
if __name__=='__main__':unittest.main()

class ChildBounds(unittest.TestCase):
    def test_success_timeout_and_output_limit(self):
        import sys, tempfile, time, subprocess
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            elapsed=m.execute([sys.executable,'-c','print('+repr(m.COMPLETE)+')'],time.monotonic()+5,root/'ok.log')
            self.assertGreater(elapsed,0)
            with self.assertRaises(subprocess.TimeoutExpired):
                m.execute([sys.executable,'-c','import time; print("before timeout",flush=True); time.sleep(5)'],time.monotonic()+.15,root/'timeout.log')
            self.assertIn('before timeout',(root/'timeout.log').read_text())
            with self.assertRaisesRegex(ValueError,'too large'):
                m.execute([sys.executable,'-c','import sys; sys.stdout.write("x"*1100000)'],time.monotonic()+5,root/'large.log')
            self.assertEqual((root/'large.log').stat().st_size,1000000)
