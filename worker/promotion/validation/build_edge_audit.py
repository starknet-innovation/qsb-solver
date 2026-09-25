"""Source-locked derivatives for exception handoff and device hit-capacity gates."""
import difflib,hashlib,json,shutil,subprocess
from pathlib import Path

N=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def once(text,old,new):
    if text.count(old)!=1:raise ValueError('diagnostic source anchor changed: '+old)
    return text.replace(old,new)


def exception_source(tree,resolve,force):
    override='    switch(idx%3){\n'+''.join('    case %d: '%i+''.join('z[%d]=0x%xULL;'%(j,(v>>(64*j))&((1<<64)-1)) for j in range(4))+'break;\n' for i,v in enumerate([0,7,N-7]))+'    }\n'
    anchor='    _FixedBaseSignedXYZZStream(qx,qy,qzz,qzzz,z,d_gt);'
    tree=once(tree,anchor,override+anchor)
    if force:tree=once(tree,'    bool usable = active && ((prod[0]|prod[1]|prod[2]|prod[3]) != 0);','    bool usable = false; // diagnostic forced handoff')
    resolve=once(resolve,'            accept=false;',r'''            fprintf(stderr,"EXACT %u",tag&((1u<<29)-1));
            for(unsigned b=0;b<2;b++){fprintf(stderr," %d:",branches[b].finite);for(auto c:branches[b].key)fprintf(stderr,"%02x",c);}fprintf(stderr,"\n");
            accept=false;''')
    return tree,resolve


def capacity_source(tree):
    tree=once(tree,'__global__ void __launch_bounds__(256, 2) kernel_digest(','__device__ __constant__ int QSB_AUDIT_HITS;\n__global__ void __launch_bounds__(256, 2) kernel_digest(')
    tree=once(tree,'    if(v){uint32_t p=atomicAdd(d_hit_cnt,1);','    v=active && idx<QSB_AUDIT_HITS; recid=0; hash_choice=0;\n    if(v){uint32_t p=atomicAdd(d_hit_cnt,1);')
    tree=once(tree,'QSB_CUDA_REQUIRE(cudaMalloc(&d_hit_idx,1024*4));',r'''QSB_CUDA_REQUIRE(cudaMalloc(&d_hit_idx,1024*4+64));
    int audit_hits=getenv("QSB_AUDIT_HITS")?atoi(getenv("QSB_AUDIT_HITS")):0;
    QSB_CUDA_REQUIRE(cudaMemcpyToSymbol(QSB_AUDIT_HITS,&audit_hits,4));
    QSB_CUDA_REQUIRE(cudaMemset(d_hit_idx+1024,0xA5,64));''')
    tree=once(tree,'QSB_CUDA_REQUIRE(cudaMalloc(&d_hit_combos, 1024 * MAX_T));',r'''QSB_CUDA_REQUIRE(cudaMalloc(&d_hit_combos, 1024 * MAX_T+64));
    QSB_CUDA_REQUIRE(cudaMemset(d_hit_combos+1024*MAX_T,0xA5,64));''')
    marker='            // Never claim complete coverage after truncating candidate records.'
    if tree.count(marker)!=2:raise ValueError('capacity anchor changed')
    pos=tree.index(marker)
    capture=r'''            {
                uint8_t guards[128];
                QSB_CUDA_REQUIRE(cudaMemcpy(guards,d_hit_idx+1024,64,cudaMemcpyDeviceToHost));
                QSB_CUDA_REQUIRE(cudaMemcpy(guards+64,d_hit_combos+1024*MAX_T,64,cudaMemcpyDeviceToHost));
                for(int j=0;j<128;j++)if(guards[j]!=0xA5){fprintf(stderr,"CANARY_CORRUPT\n");return 3;}
                unsigned count=h_hit<1024?h_hit:1024;
                uint32_t tags[1024];uint8_t combos[1024*MAX_T];
                QSB_CUDA_REQUIRE(cudaMemcpy(tags,d_hit_idx,count*4,cudaMemcpyDeviceToHost));
                QSB_CUDA_REQUIRE(cudaMemcpy(combos,d_hit_combos,count*MAX_T,cudaMemcpyDeviceToHost));
                printf("DEVICE_COUNT %u CANARIES_OK\n",h_hit);
                for(unsigned j=0;j<count;j++){
                    printf("DEVICE_REC %u",tags[j]&0x3FFFFFFF);
                    for(int k=0;k<t_sel;k++)printf(" %u",combos[j*MAX_T+k]);
                    printf("\n");
                }
            }
'''
    return tree[:pos]+capture+tree[pos:]


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    root=Path('/src');source=root/'research/optimized-subset';lockfile=root/'worker/optimized/source-lock.json';lock=json.loads(lockfile.read_text())
    actual={str(p.relative_to(source)):sha(p) for p in (source/'subset').rglob('*') if p.is_file()}
    if actual!=lock['files']:raise ValueError('source lock mismatch')
    out=Path('/opt/qsb-edge-audit');out.mkdir()
    patches={}
    for mode in ['capacity','forced-exception','detected-exception']:
        target=Path('/tmp')/('qsb-audit-'+mode);shutil.copytree(source,target)
        tree=target/'subset/tests/gpu_epochs/tree.cu';resolve=tree.with_name('exact_resolve.cuh');original=tree.read_text();orig_resolve=resolve.read_text()
        if mode=='capacity':tree.write_text(capacity_source(original))
        else:
            a,b=exception_source(original,orig_resolve,mode=='forced-exception');tree.write_text(a);resolve.write_text(b)
        patch=''.join(difflib.unified_diff(original.splitlines(True),tree.read_text().splitlines(True),fromfile='locked/tree.cu',tofile=mode+'/tree.cu'))+''.join(difflib.unified_diff(orig_resolve.splitlines(True),resolve.read_text().splitlines(True),fromfile='locked/exact_resolve.cuh',tofile=mode+'/exact_resolve.cuh'))
        (out/(mode+'.diff')).write_text(patch)
        subprocess.run(['nvcc',*lock['flags'],'-o',str(out/mode),str(target/'subset/subset.cu'),'-lcrypto','-lm'],check=True)
    build=json.loads(Path('/opt/qsb-validation/build-receipt.json').read_text())
    receipt=dict(sourceLockSha256=sha(lockfile),sourceFiles=actual,flags=lock['flags'],unmodifiedBinarySha256=build['binarySha256'],files={p.name:sha(p) for p in out.iterdir()},compiler=subprocess.check_output(['nvcc','--version'],text=True),scope='Diagnostic synthetic scalar/point and hit injection only; normal solver unchanged',status='UNEXECUTED')
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':main()
