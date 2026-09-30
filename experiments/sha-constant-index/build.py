"""Compile but never execute CUDA; retain PTX/SASS for no-op pruning."""
import hashlib,json,subprocess
from pathlib import Path
from prepare import ROOT,SOURCE,EXPECTED,function,transform
OUT=Path('/results');OUT.mkdir(exist_ok=False)
original=SOURCE.read_text();changed=transform(original)
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
for name,text,shape in [('baseline',original,'[4][64]'),('candidate',changed,'[256]')]:
 body='__device__ __constant__ uint32_t QSB_CONST_SCHEDULE'+shape+';\n'+function(text)+'\n'
 parts.append('namespace '+name+' {\n'+body+'}\n')
 standalone=header+body+'''extern "C" __global__ void compression(uint32_t *states){
 unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
 qsb_compress_constant_rolled(states+i*8);
}\n'''
 path=OUT/(name+'.cu');path.write_text(standalone)
 for kind in ['ptx','cubin']:
  subprocess.run(['nvcc','-O3','-arch=sm_86','-std=c++17','--'+kind,str(path),'-o',str(OUT/(name+'.'+kind))],check=True)
 (OUT/(name+'.sass')).write_bytes(subprocess.check_output(['cuobjdump','--dump-sass',str(OUT/(name+'.cubin'))]))
harness=OUT/'compression-gate.cu';harness.write_text(header+''.join(parts)+Path(__file__).with_name('harness.cu.inc').read_text())
subprocess.run(['nvcc','-O3','-arch=sm_86','-std=c++17',str(harness),'-o',str(OUT/'compression-gate')],check=True)
(OUT/'build.json').write_text(json.dumps({'baselineSourceSha256':EXPECTED,'candidateSourceSha256':hashlib.sha256(changed.encode()).hexdigest(),'compiler':subprocess.check_output(['nvcc','--version'],text=True),'files':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in OUT.iterdir() if p.is_file()},'gpuExecuted':False,'status':'UNEXECUTED'},indent=2)+'\n')
