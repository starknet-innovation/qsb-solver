"""Prepare a public-table-only GPU comparison changing only host ladders."""
import argparse
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
TREE='research/optimized-subset/subset/tests/gpu_epochs/tree.cu'
MATH='research/optimized-subset/subset/GPUMath.h'
CHECK='research/optimized-subset/subset/tests/gpu_epochs/openssl_checked.h'
INPUTS={TREE:'71e4b01469b2d2327c32bc62d4b20d1a6276c20c994cf6c3e8a082e9abac7cdb',MATH:'86ade5d707770870ba29994c20cbd12c3d98a29036fb7f48d93ba00c13bd3b12',CHECK:'82de4a9eaa07c7e9b93bfce060067cbcc32c858c10e1c6d77475b168c1cc069b'}
CANDIDATE_SHA='5ba19891831528121c4c5c69bd2f24eddda23ba8a44f50cb1e4dd7a9c7bf16f5'
def sha(data):return hashlib.sha256(data).hexdigest()
def extract(text,start,end):
    if text.count(start)!=1 or text.count(end)!=1:raise ValueError('ambiguous extraction')
    return text[text.index(start):text.index(end,text.index(start))]
def prepare(output,root=ROOT,here=HERE):
    inputs={p:(root/p).read_bytes() for p in INPUTS}
    if any(sha(inputs[p])!=digest for p,digest in INPUTS.items()):raise ValueError('frozen baseline source changed')
    candidate=(here/'candidate.cpp.inc').read_bytes()
    if sha(candidate)!=CANDIDATE_SHA:raise ValueError('frozen host candidate changed')
    text=inputs[TREE].decode()
    kernel=extract(text,'__global__ void kernel_build_gtable(','/* ============================================================\n * Host code')
    geometry=extract(text,'/* ZLAB_T14 (kill switch','/* n = secp256k1 group order')
    host=extract(text,'/* Affine (x,y) of a point','/* OpenSSL fallback builder')
    prefix='// Public table experiment; upstream GPL-3.0 source retained. See LICENSE.\n#include <cuda_runtime.h>\n#include <cstdint>\n#include <cstdio>\n#include <cstdlib>\n#include <cstring>\n#include <vector>\n#include <chrono>\n#include <openssl/ec.h>\n#include <openssl/bn.h>\n#include <openssl/obj_mac.h>\n#include <openssl/sha.h>\n#include "GPUMath.h"\n#include "openssl_checked.h"\n#if defined(OPENSSL_NO_DEPRECATED_3_0)\n#error EC_POINTs_make_affine required; experiment only\n#endif\n'
    identity='#define ORIGINAL_KERNEL_SHA256 "'+sha(kernel.encode())+'"\n'
    outputs={'table-gate.cu':(prefix+identity+geometry+kernel+host+candidate.decode()+(here/'gpu-harness.cu.inc').read_text()).encode(),'original-kernel.cu.inc':kernel.encode(),'GPUMath.h':inputs[MATH],'openssl_checked.h':inputs[CHECK],'LICENSE':(root/'research/optimized-subset/LICENSE').read_bytes()}
    output.mkdir(parents=True,exist_ok=False)
    for name,data in outputs.items():(output/name).write_bytes(data)
    manifest={'schema':1,'scope':'host-ladder-only candidate; identical baseline GPU kernel both arms','baseline_inputs':INPUTS,'host_candidate_sha256':CANDIDATE_SHA,'original_kernel_sha256':sha(kernel.encode()),'kernel_changed':False,'experiment_sources':{p:sha((here/p).read_bytes()) for p in ['prepare_gpu.py','candidate.cpp.inc','gpu-harness.cu.inc']},'outputs':{p:sha(data) for p,data in outputs.items()},'status':'prepared-not-native-validated'}
    (output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=Path);prepare(p.parse_args().output)
