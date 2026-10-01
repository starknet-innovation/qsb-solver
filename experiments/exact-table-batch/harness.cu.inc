// This executable constructs public elliptic-curve tables only. No search,
// recovery, transaction, wallet, or fixture parsing code is included.
#include <chrono>
#include <vector>
#include <openssl/sha.h>
#define CK(call) do { cudaError_t err=(call); if(err!=cudaSuccess) { fprintf(stderr,"CUDA %s:%d %s\n",__FILE__,__LINE__,cudaGetErrorString(err)); exit(2); } } while(0)
static double clock_ms() {
    return std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now().time_since_epoch()).count();
}
struct Sample { float kernel_ms; double construction_ms; };
static Sample launch(bool candidate,uint64_t *dL,uint64_t *dH,uint8_t *out,bool padding=false) {
    cudaEvent_t a,b; CK(cudaEventCreate(&a)); CK(cudaEventCreate(&b));
    CK(cudaMemset(out,candidate?0xa5:0x5a,(size_t)GT_TOTAL_ENTRIES*64));
    CK(cudaEventRecord(a));
    if(candidate) candidate_build_gtable<<<(GT_TOTAL_ENTRIES+255)/256+(padding?1:0),256>>>(dL,dH,out);
    else baseline_build_gtable<<<(GT_TOTAL_ENTRIES+255)/256+(padding?1:0),256>>>(dL,dH,out);
    CK(cudaGetLastError()); CK(cudaEventRecord(b)); CK(cudaEventSynchronize(b));
    float ms; CK(cudaEventElapsedTime(&ms,a,b));
    CK(cudaEventDestroy(a)); CK(cudaEventDestroy(b));
    return {ms,0};
}
static void compare(const std::vector<uint8_t>& a,const std::vector<uint8_t>& b) {
    if(a!=b) {
        size_t i=0; while(i<a.size() && a[i]==b[i]) ++i;
        fprintf(stderr,"full table mismatch: record=%zu byte=%zu\n",i/64,i%64); exit(3);
    }
}
static void digest(const std::vector<uint8_t>& bytes,char hex[65]) {
    unsigned char h[32]; SHA256(bytes.data(),bytes.size(),h);
    for(int k=0;k<32;k++) sprintf(hex+2*k,"%02x",h[k]); hex[64]=0;
}
static void upload(const std::vector<uint64_t>& L,const std::vector<uint64_t>& H,uint64_t **dL,uint64_t **dH) {
    CK(cudaMalloc(dL,L.size()*8)); CK(cudaMalloc(dH,H.size()*8));
    CK(cudaMemcpy(*dL,L.data(),L.size()*8,cudaMemcpyHostToDevice));
    CK(cudaMemcpy(*dH,H.data(),H.size()*8,cudaMemcpyHostToDevice));
}
static Sample construction(const uint8_t scalar[32],bool candidate,std::vector<uint8_t>& out) {
    double before=clock_ms();
    std::vector<uint64_t> L((size_t)GT_CHUNKS*GT_LO*8),H((size_t)GT_CHUNKS*GT_HI*8);
    gt_build_ladders(L.data(),H.data(),scalar);
    uint64_t *dL,*dH; uint8_t *dt; upload(L,H,&dL,&dH); CK(cudaMalloc(&dt,out.size()));
    Sample s=launch(candidate,dL,dH,dt);
    CK(cudaMemcpy(out.data(),dt,out.size(),cudaMemcpyDeviceToHost));
    if(!gt_spot_check(out.data(),GT_CHUNKS*4+192,scalar)) exit(4);
    CK(cudaFree(dL)); CK(cudaFree(dH)); CK(cudaFree(dt));
    s.construction_ms=clock_ms()-before; return s;
}
int main(int argc,char **argv) {
    if(argc!=2 && !(argc==3 && strcmp(argv[2],"--correctness-only")==0)) {
        fprintf(stderr,"usage: table-gate OUTPUT.json [--correctness-only]\n"); return 1;
    }
    const bool correctness_only=argc==3;
    FILE *report=fopen(argv[1],"wx"); if(!report){perror("report");return 1;}
    cudaDeviceProp props; CK(cudaGetDeviceProperties(&props,0));
    CK(cudaSetDevice(0)); CK(cudaFree(0));
    const size_t bytes=(size_t)GT_TOTAL_ENTRIES*64;
    std::vector<uint8_t> baseline(bytes),candidate(bytes);
    // Public fixed nonzero scalars: 1, 17, and a dense 248-bit integer.
    uint8_t scalars[3][32]={{1},{17},{0}};
    for(int k=0;k<31;k++) scalars[2][k]=(uint8_t)(k*7+3);
    char hashes[3][65];
    for(int k=0;k<3;k++) {
        construction(scalars[k],false,baseline);
        construction(scalars[k],true,candidate);
        compare(baseline,candidate); digest(candidate,hashes[k]);
    }
    // Inject affine equal/opposite inputs. Baseline defines exceptional record
    // behavior; compare ALL bytes, including neighboring unaffected records.
    std::vector<uint64_t> L((size_t)GT_CHUNKS*GT_LO*8),H((size_t)GT_CHUNKS*GT_HI*8);
    gt_build_ladders(L.data(),H.data(),scalars[0]);
    for(int ch=0;ch<GT_CHUNKS;ch++) {
        memcpy(&H[((size_t)ch*GT_HI+1)*8],&L[((size_t)ch*GT_LO+1)*8],64);
        uint64_t *dst=&H[((size_t)ch*GT_HI+2)*8];
        memcpy(dst,&L[((size_t)ch*GT_LO+3)*8],64);
        BIGNUM *p=BN_new(),*y=BN_lebin2bn((unsigned char*)(dst+4),32,NULL);
        QSB_SSL_PTR(p); QSB_SSL_PTR(y);
        QSB_SSL_SIZE(BN_hex2bn(&p,"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),64);
        QSB_SSL_OK(BN_sub(y,p,y)); QSB_SSL_SIZE(BN_bn2lebinpad(y,(unsigned char*)(dst+4),32),32);
        BN_free(p);BN_free(y);
    }
    uint64_t *dL,*dH; uint8_t *dt; upload(L,H,&dL,&dH); CK(cudaMalloc(&dt,bytes));
    launch(false,dL,dH,dt,true); CK(cudaMemcpy(baseline.data(),dt,bytes,cudaMemcpyDeviceToHost));
    launch(true,dL,dH,dt,true); CK(cudaMemcpy(candidate.data(),dt,bytes,cudaMemcpyDeviceToHost));
    compare(baseline,candidate); CK(cudaFree(dL));CK(cudaFree(dH));CK(cudaFree(dt));
    // Timing starts only after differential/independent OpenSSL checks.
    // Seven alternating paired construction samples; kernel CUDA events and
    // complete ladder/upload/build/download/spot-check wall times are distinct.
    fprintf(report,"{\"status\":\"passed\",\"geometry\":%d,\"records_per_table\":%u,\"full_tables_compared\":4,\"exceptional_inputs\":%d,\"openssl_samples_per_table\":%d,\"table_sha256\":[\"%s\",\"%s\",\"%s\"],\"gpu\":\"%s\",\"timingExecuted\":%s,\"samples\":[",GT_CHUNKS,GT_TOTAL_ENTRIES,GT_CHUNKS*2,GT_CHUNKS*4+192,hashes[0],hashes[1],hashes[2],props.name,correctness_only?"false":"true");
    int number=0;
    for(int pair=0;pair<(correctness_only?0:7);pair++) {
        for(int order=0;order<2;order++) {
            bool is_candidate=(pair+order)%2;
            Sample s=construction(scalars[0],is_candidate,is_candidate?candidate:baseline);
            fprintf(report,"%s{\"pair\":%d,\"order\":%d,\"binary\":\"%s\",\"kernel_ms\":%.6f,\"construction_ms\":%.6f}",number++?",":"",pair,order,is_candidate?"candidate":"baseline",s.kernel_ms,s.construction_ms);
        }
        compare(baseline,candidate);
    }
    fprintf(report,"]}\n"); if(fclose(report)!=0) return 5;
    puts("Exact full-table differential and independent OpenSSL samples passed; receipt saved.");
    return 0;
}
