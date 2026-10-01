"""Create an isolated hash-bound table construction experiment; never run a solver."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
TREE = "research/optimized-subset/subset/tests/gpu_epochs/tree.cu"
INPUTS = {
    TREE: "71e4b01469b2d2327c32bc62d4b20d1a6276c20c994cf6c3e8a082e9abac7cdb",
    "research/optimized-subset/subset/GPUMath.h": "86ade5d707770870ba29994c20cbd12c3d98a29036fb7f48d93ba00c13bd3b12",
    "research/optimized-subset/subset/tests/gpu_epochs/openssl_checked.h": "82de4a9eaa07c7e9b93bfce060067cbcc32c858c10e1c6d77475b168c1cc069b",
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load_inputs(root):
    result = {}
    for name, expected in INPUTS.items():
        data = (root / name).read_bytes()
        if sha(data) != expected:
            raise ValueError(f"Frozen baseline input changed: {name}")
        result[name] = data
    return result

def extract(source, start, end):
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError("Ambiguous source extraction boundary")
    offset = source.index(start)
    return source[offset:source.index(end, offset)]

def prepare(output, root=ROOT):
    inputs = load_inputs(root)
    original = inputs[TREE].decode()
    baseline = extract(original, "__global__ void kernel_build_gtable(", "/* ============================================================\n * Host code")
    candidate = (HERE / "kernel.cu.inc").read_text()
    changed = original.replace(baseline, candidate + "\n", 1)
    geometry = extract(original, "/* ZLAB_T14 (kill switch", "/* n = secp256k1 group order")
    host = extract(original, "/* Affine (x,y) of a point", "/* OpenSSL fallback builder")
    harness = '#include <cuda_runtime.h>\n#include <cstdint>\n#include <cstdio>\n#include <cstdlib>\n#include <cstring>\n#include <openssl/bn.h>\n#include <openssl/ec.h>\n#include <openssl/obj_mac.h>\n#include "GPUMath.h"\n#include "openssl_checked.h"\n'
    harness += geometry + baseline.replace("kernel_build_gtable", "baseline_build_gtable")
    harness += candidate.replace("kernel_build_gtable", "candidate_build_gtable") + host
    harness += (HERE / "harness.cu.inc").read_text()
    files = {
        "candidate-tree.cu": changed.encode(),
        "table-gate.cu": harness.encode(),
        "candidate.patch": "".join(difflib.unified_diff(original.splitlines(True), changed.splitlines(True), fromfile="a/"+TREE, tofile="b/"+TREE)).encode(),
        "GPUMath.h": inputs["research/optimized-subset/subset/GPUMath.h"],
        "openssl_checked.h": inputs["research/optimized-subset/subset/tests/gpu_epochs/openssl_checked.h"],
    }
    output.mkdir(parents=True, exist_ok=False)
    for name, data in files.items():
        (output / name).write_bytes(data)
    manifest = {"schema": 1, "status": "prepared-not-native-validated", "baseline_inputs": INPUTS,
                "experiment_sources": {name: sha((HERE/name).read_bytes()) for name in ("prepare.py", "kernel.cu.inc", "harness.cu.inc")},
                "outputs": {name: sha(data) for name, data in files.items()},
                "arithmetic": "unchanged baseline GPUMath.h", "batch_width": 32,
                "candidate_scope": "kernel_build_gtable only; no solver execution in gate"}
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")
    return manifest

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    prepare(args.output)
