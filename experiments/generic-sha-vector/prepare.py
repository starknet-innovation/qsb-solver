"""Extract the two exact compression functions into a native CUDA differential gate."""
from pathlib import Path
import hashlib
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'research/optimized-subset/subset/tests/gpu_epochs/tree.cu'
EXPECTED='71e4b01469b2d2327c32bc62d4b20d1a6276c20c994cf6c3e8a082e9abac7cdb'
def function(s):
    start=s.index('__device__ __forceinline__ void qsb_compress_generic_tail(')
    return s[start:s.index('\n__global__',start)]
def main():
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('output',type=Path);args=parser.parse_args()
    original=SOURCE.read_bytes()
    if hashlib.sha256(original).hexdigest()!=EXPECTED:
        raise ValueError('Baseline source hash mismatch')
    with tempfile.TemporaryDirectory() as tmp:
        p=Path(tmp)/'subset/tests/gpu_epochs/tree.cu';p.parent.mkdir(parents=True);p.write_bytes(original)
        subprocess.run(['patch','--batch','-p1','-i',str(Path(__file__).with_name('generic-tail-vector.patch'))],cwd=tmp,check=True)
        changed=p.read_text()
    header='''#include <cuda_runtime.h>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <vector>
__host__ __device__ uint32_t rr(uint32_t x,int n){return(x>>n)|(x<<(32-n));}
#define S0(x) (rr(x,2)^rr(x,13)^rr(x,22))
#define S1(x) (rr(x,6)^rr(x,11)^rr(x,25))
#define Ch(x,y,z) ((x&y)^(~x&z))
#define Maj(x,y,z) ((x&y)^(x&z)^(y&z))
#define S2Round(a,b,c,d,e,f,g,h,k,w) t1=h+S1(e)+Ch(e,f,g)+k+(w);t2=S0(a)+Maj(a,b,c);d+=t1;h=t1+t2;
#define CK(x) do{cudaError_t err=(x);if(err!=cudaSuccess){fprintf(stderr,"CUDA %s:%d %s\\n",__FILE__,__LINE__,cudaGetErrorString(err));exit(2);}}while(0)
'''
    parts=[]
    for name,src in [('baseline',original.decode()),('candidate',changed)]:
        parts.append('namespace '+name+' {\n__device__ const uint32_t *QSB_GENERIC_TAIL_SCHEDULE;\n'+function(src)+'\n}\n')
    harness=Path(__file__).with_name('harness.cu.inc').read_text()
    with args.output.open('x') as f:f.write(header+''.join(parts)+harness)
if __name__=='__main__':main()
