import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).parents[1]
def load(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'worker/promotion/validation'/f'{name}.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

class Audit(unittest.TestCase):
    def test_instrumentation_host_only(self):
        import subprocess
        subprocess.run(['python3',str(ROOT/'worker/prepare_kernels.py')],check=True,capture_output=True)
        spec=importlib.util.spec_from_file_location('repair',ROOT/'worker/promotion/prepare_pinning.py')
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        original=(ROOT/'worker/build/pinning/pinning.cu').read_text()
        repaired,_=module.repair(original)
        diagnostic=load('build_pinning_audit').instrument(repaired)
        self.assertTrue(diagnostic.startswith(original[:original.index('int main(')]))
        self.assertNotIn('QSB_AUDIT_FAIL',repaired)
        self.assertEqual(diagnostic.count('if(getenv("QSB_AUDIT_OVERFLOW")) h_hit=65;'),2)
        for anchor in ['h_hit = hit_report[0];','QSB_PIN_CUDA_REQUIRE(cudaMemcpy(&h_hit, d_hit_cnt, 4, cudaMemcpyDeviceToHost));']:
            tail=diagnostic[diagnostic.index(anchor):]
            self.assertLess(tail.index('QSB_AUDIT_OVERFLOW'),tail.index('if (h_hit > 0)'))

    def test_failure_rejects_false_completion_and_later_calls(self):
        validate=load('run_pinning_audit').validate_failure
        good=dict(exit=2,stdout='',stderr='QSB_AUDIT_CALL 1 cudaSetDevice(0)\nQSB_RANGE_INCOMPLETE',hits={})
        validate(good,[('1','cudaSetDevice(0)')])
        for change in [dict(exit=0),dict(stdout='Done:'),dict(hits={'hit':'x'}),dict(stderr='error')]:
            with self.assertRaises(ValueError):validate({**good,**change})
        with self.assertRaises(ValueError):validate(good,[])
