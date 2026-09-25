import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).parents[1]

class PinningOutput(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('c++')
        if not compiler:
            raise unittest.SkipTest('C++ compiler unavailable')
        cls.tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.tmp.cleanup)
        root = Path(cls.tmp.name)
        (root/'test.cpp').write_text('#include "pinning_output.h"\n#include <stdlib.h>\nint main(int argc,char**argv){uint32_t hits[64];for(int i=0;i<64;i++)hits[i]=i|0xc0000000;return qsb_publish_pinning_hits(argv[1],2147483648u,500000000,hits,strtoul(argv[2],0,10))?0:2;}')
        cls.binary = root/'test'
        subprocess.run([compiler,'-I'+str(ROOT/'worker/promotion'),str(root/'test.cpp'),'-o',str(cls.binary)],check=True)

    def test_capacity_and_records(self):
        for count in [0,1,63,64,65]:
            with tempfile.TemporaryDirectory() as tmp:
                out = Path(tmp)/'hits'
                result = subprocess.run([str(self.binary),str(out),str(count)])
                self.assertEqual(result.returncode, 2 if count>64 else 0)
                if count>64:
                    self.assertFalse(out.exists())
                else:
                    expected=''.join(f'sequence=2147483648\nlocktime={500000000+i}\nhash_choice=1\nrecid=1\n' for i in range(count))
                    self.assertEqual(out.read_text(),expected)

    def test_open_failure_rejects(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(subprocess.run([str(self.binary),tmp,'1']).returncode,2)

    @unittest.skipUnless(Path('/dev/full').exists(), 'Linux full device required')
    def test_buffered_close_failure_rejects(self):
        self.assertEqual(subprocess.run([str(self.binary),'/dev/full','1']).returncode,2)

    def test_prepared_active_cuda_calls_are_guarded(self):
        subprocess.run(['python3',str(ROOT/'worker/prepare_kernels.py')],check=True,capture_output=True)
        spec=importlib.util.spec_from_file_location('repair',ROOT/'worker/promotion/prepare_pinning.py')
        repair=importlib.util.module_from_spec(spec);spec.loader.exec_module(repair)
        source=(ROOT/'worker/build/pinning/pinning.cu').read_text()
        fixed,sites=repair.repair(source)
        for call in ['cudaMemset(d_hit_cnt, 0, 4)','cudaMemcpy(&h_hit, d_hit_cnt, 4, cudaMemcpyDeviceToHost)','cudaMemcpy(hits, d_hit_idx, nh*4, cudaMemcpyDeviceToHost)','cudaMalloc(&d_hit_cnt, 4)','cudaMalloc(&dH,hb)']:
            self.assertIn(call,sites)
            self.assertIn('QSB_PIN_CUDA_REQUIRE('+call+')',fixed)
        self.assertEqual(len(sites),39)
        self.assertNotIn('int nh = (h_hit > 64) ? 64 : h_hit;',fixed)
        self.assertIn('if (!qsb_publish_pinning_hits',fixed)
        # Device kernels precede main and remain byte-for-byte unchanged.
        self.assertTrue(fixed.startswith(source[:source.index('int main(')]))
