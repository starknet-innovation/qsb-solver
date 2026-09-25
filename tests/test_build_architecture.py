import importlib.util
import json
import hashlib
import tempfile
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('optimized_build', ROOT/'worker/optimized/build.py')
build = importlib.util.module_from_spec(spec); spec.loader.exec_module(build)

class Architecture(unittest.TestCase):
    def test_default_preserves_every_locked_flag(self):
        flags=json.loads((ROOT/'worker/optimized/source-lock.json').read_text())['flags']
        self.assertEqual(build.architecture_flags(flags,'89'),flags)

    def test_a10_changes_only_architecture(self):
        flags=json.loads((ROOT/'worker/optimized/source-lock.json').read_text())['flags']
        effective=build.architecture_flags(flags,'86')
        self.assertEqual([(a,b) for a,b in zip(flags,effective) if a!=b],[('-arch=sm_89','-arch=sm_86')])
        self.assertIn('-arch=sm_89',flags)

    def test_unsupported_targets_and_ambiguous_flags_reject(self):
        for architecture in ('', 'native', '80', '90', '86;echo', None, 86):
            with self.assertRaises(ValueError):build.architecture_flags(['-arch=sm_89'],architecture)
        for flags in ([],['-arch=sm_89']*2,['-arch=sm_86'],['-arch=sm_89','-arch=sm_86'],['-arch=sm_89','-gencode=arch=compute_89,code=sm_89'],['-arch=sm_89','--gpu-code=sm_89']):
            with self.assertRaises(ValueError):build.architecture_flags(flags,'86')


bind_spec = importlib.util.spec_from_file_location('promotion_bind', ROOT/'worker/promotion/bind.py')
binder = importlib.util.module_from_spec(bind_spec)
bind_spec.loader.exec_module(binder)

class CombinedArchitecture(unittest.TestCase):
    def test_matching_and_mixed_architecture_images(self):
        for pin, subset, target, accepted in [('86','86','86',True), ('89','89','89',True), ('86','89','86',False), ('89','86','86',False)]:
            with self.subTest(pin=pin,subset=subset,target=target), tempfile.TemporaryDirectory() as directory:
                root=Path(directory)
                (root/'source/pinning').mkdir(parents=True)
                (root/'source/pinning/cuda-architecture').write_text(pin)
                for name in ('pinning','subset','handler.py','historical_handler.py','search_ranges.py'):
                    (root/name).write_bytes(b'public test artifact')
                receipt=dict(architecture='sm_'+subset, flags=['-O3','-arch=sm_'+subset], binarySha256=hashlib.sha256((root/'subset').read_bytes()).hexdigest(),sourceLockSha256='d'*64)
                (root/'optimized-build-receipt.json').write_text(json.dumps(receipt))
                if accepted:
                    binder.bind(root,'a'*40,target)
                    self.assertEqual(json.loads((root/'pipeline.json').read_text())['architecture'],'sm_'+target)
                else:
                    with self.assertRaises(ValueError):binder.bind(root,'a'*40,target)
                    self.assertFalse((root/'pipeline.json').exists())
