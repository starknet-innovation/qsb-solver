"""Extract only frozen public point-ladder helpers; no solver executable."""
import hashlib
import json
from pathlib import Path
import argparse
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
TREE = 'research/optimized-subset/subset/tests/gpu_epochs/tree.cu'
CHECK = 'research/optimized-subset/subset/tests/gpu_epochs/openssl_checked.h'
INPUTS = {TREE: '71e4b01469b2d2327c32bc62d4b20d1a6276c20c994cf6c3e8a082e9abac7cdb', CHECK: '82de4a9eaa07c7e9b93bfce060067cbcc32c858c10e1c6d77475b168c1cc069b'}
def sha(x): return hashlib.sha256(x).hexdigest()
def between(text, a, b):
    if text.count(a)!=1 or text.count(b)!=1: raise ValueError('ambiguous extraction')
    return text[text.index(a):text.index(b,text.index(a))]
def prepare(out, root=ROOT):
    data={p:(root/p).read_bytes() for p in INPUTS}
    if any(sha(data[p])!=v for p,v in INPUTS.items()): raise ValueError('frozen source changed')
    src=data[TREE].decode()
    geometry=between(src,'/* ZLAB_T14 (kill switch','/* n = secp256k1 group order')
    host=between(src,'/* Affine (x,y) of a point','/* Spot-check the built table')
    prefix='// Isolated public math experiment; extracted upstream GPL-3.0 source. See LICENSE.\n#include <cstdint>\n#include <cstring>\n#include <cstdio>\n#include <cstdlib>\n#include <vector>\n#include <array>\n#include <chrono>\n#include <openssl/ec.h>\n#include <openssl/bn.h>\n#include <openssl/obj_mac.h>\n#include <openssl/crypto.h>\n#include "openssl_checked.h"\n#define __host__\n#define __device__\n#define __forceinline__ inline\n#if defined(OPENSSL_NO_DEPRECATED_3_0)\n#error EC_POINTs_make_affine unavailable; do not substitute a different algorithm\n#endif\n'
    outputs={'ladder.cpp':(prefix+geometry+host+(HERE/'candidate.cpp.inc').read_text()+(HERE/'harness.cpp.inc').read_text()).encode(),'openssl_checked.h':data[CHECK],'LICENSE':(root/'research/optimized-subset/LICENSE').read_bytes()}
    out.mkdir(parents=True,exist_ok=False)
    for p,v in outputs.items(): (out/p).write_bytes(v)
    manifest={'schema':1,'scope':'public-point-ladder-only','baseline_inputs':INPUTS,'sources':{p:sha((HERE/p).read_bytes()) for p in ['prepare.py','candidate.cpp.inc','harness.cpp.inc']},'outputs':{p:sha(v) for p,v in outputs.items()}}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=Path);prepare(p.parse_args().output)
