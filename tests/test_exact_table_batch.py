import importlib.util
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("exact_batch", ROOT/"experiments/exact-table-batch/prepare.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
P = 2**256-2**32-977


def batch_inverse(values):
    """CPU specification for the shared product tree and zero exclusion."""
    if len(values) != 32:
        raise ValueError("warp width")
    tree = [0]*64
    tree[32:] = [v % P or 1 for v in values]
    for i in range(31,0,-1):
        tree[i] = tree[2*i]*tree[2*i+1] % P
    tree[1] = pow(tree[1], -1, P)
    for i in range(1,32):
        inverse, left, right = tree[i], tree[2*i], tree[2*i+1]
        tree[2*i] = inverse*right % P
        tree[2*i+1] = inverse*left % P
    return [inv if v % P else 0 for inv,v in zip(tree[32:],values)]


class ExactTableBatchTests(unittest.TestCase):
    def test_montgomery_identity_zero_and_boundaries(self):
        rng = random.Random(71)
        cases = [[0]*32, [1]*32, [P]*32,
                 [0,1,P-1,P,P+1]+[rng.randrange(1,P) for _ in range(27)]]
        cases += [[rng.randrange(P) for _ in range(32)] for _ in range(32)]
        for values in cases:
            self.assertEqual(batch_inverse(values),[pow(v,-1,P) if v%P else 0 for v in values])

    def test_zero_lane_does_not_change_neighbors(self):
        original = list(range(1,33))
        expected = batch_inverse(original)
        for index in range(32):
            changed = original.copy(); changed[index] = 0
            want = expected.copy(); want[index] = 0
            self.assertEqual(batch_inverse(changed),want)

    def test_source_drift_prevents_any_output(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)/"root"; out=Path(d)/"out"
            p=root/m.TREE; p.parent.mkdir(parents=True); p.write_text("drift")
            with self.assertRaisesRegex(ValueError,"Frozen baseline input changed"):
                m.prepare(out,root)
            self.assertFalse(out.exists())

    def test_deterministic_isolated_patch_and_harness(self):
        before=(ROOT/m.TREE).read_bytes()
        with tempfile.TemporaryDirectory() as d:
            p=Path(d); a=p/"a"; b=p/"b"
            ma=m.prepare(a); mb=m.prepare(b)
            self.assertEqual(ma,mb)
            for name in ma["outputs"]:
                self.assertEqual((a/name).read_bytes(),(b/name).read_bytes())
                self.assertEqual(m.sha((a/name).read_bytes()),ma["outputs"][name])
            patch_root=p/"patched"; tree=patch_root/m.TREE
            tree.parent.mkdir(parents=True); tree.write_bytes(before)
            subprocess.run(["patch","--batch","-p1","-i",str(a/"candidate.patch")],cwd=patch_root,check=True,capture_output=True)
            self.assertEqual(tree.read_bytes(),(a/"candidate-tree.cu").read_bytes())
            original=before.decode(); changed=tree.read_text()
            start="__global__ void kernel_build_gtable("
            end="/* ============================================================\n * Host code"
            self.assertEqual(original[:original.index(start)],changed[:changed.index("/* Independent experiment:")])
            self.assertEqual(original[original.index(end):],changed[changed.index(end):])
            gate=(a/"table-gate.cu").read_text()
            self.assertIn("baseline_build_gtable",gate)
            self.assertIn("candidate_build_gtable",gate)
            self.assertIn("cudaMemset(out,candidate?0xa5:0x5a",gate)
            self.assertIn("gt_spot_check",gate)
            self.assertIn('strcmp(argv[2],"--correctness-only")==0',gate)
            self.assertIn("timingExecuted",gate)
            self.assertIn('correctness_only?"false":"true"',gate)
            self.assertIn("pair<(correctness_only?0:7)",gate)
            self.assertNotIn("kernel_digest",gate)
            self.assertNotIn("int main(int argc",gate[:gate.index("// This executable")])
            with self.assertRaises(FileExistsError): m.prepare(a)
        self.assertEqual((ROOT/m.TREE).read_bytes(),before)

    def test_actual_geometry_coverage(self):
        # Check every record of both layouts against the unchanged kernel mapping.
        for counts in ([2**17]+[2**16]*14,[2**18]*4+[2**17]*10):
            offset=0
            for ch,count in enumerate(counts):
                for d in range(count):
                    t=offset+d
                    observed=(0 if t<2**17 else 1+(t-2**17)//2**16) if len(counts)==15 else (t//2**18 if t<4*2**18 else 4+(t-4*2**18)//2**17)
                    self.assertEqual(observed,ch)
                    hi,lo=divmod(2*d+1,256)
                    self.assertEqual(lo%2,1)
                    self.assertLess(hi,1024 if len(counts)==15 else 2048)
                offset+=count
