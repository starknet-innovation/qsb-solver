import importlib.util,tempfile,time,unittest,sys
from pathlib import Path
ROOT=Path(__file__).parents[1]
spec=importlib.util.spec_from_file_location('edge_runner',ROOT/'worker/promotion/validation/run_edge_audit.py');runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
class EdgeRunner(unittest.TestCase):
    def test_separate_error_stream_cannot_corrupt_record(self):
        with tempfile.TemporaryDirectory() as tmp:
            program=Path(tmp)/'child'
            program.write_text('#!'+sys.executable+'\nimport sys\nsys.stdout.write("DEVICE_REC 1 ");sys.stdout.flush()\nsys.stderr.write("QSB_RANGE_INCOMPLETE: test\\n");sys.stderr.flush()\nsys.stdout.write("2 3\\n");sys.stdout.flush()\nsys.exit(2)\n');program.chmod(0o700)
            row=runner.run(program,'AA==',[],time.monotonic()+5)
            self.assertEqual(row['exit'],2)
            self.assertEqual(row['log'].splitlines()[0],'DEVICE_REC 1 2 3')
            self.assertIn('QSB_RANGE_INCOMPLETE: test',row['log'])
    def test_rank_endpoints(self):
        import math
        self.assertEqual(runner.unrank(0),list(range(9)))
        self.assertEqual(runner.unrank(math.comb(150,9)-1),list(range(141,150)))
