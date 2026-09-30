// Only fixed public tables; both arms launch the exact same original kernel.
#define CK(call) do { cudaError_t e=(call); if(e!=cudaSuccess){fprintf(stderr,"CUDA %s:%d %s\n",__FILE__,__LINE__,cudaGetErrorString(e));exit(2);} } while(0)
static double wall_ms(){return std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now().time_since_epoch()).count();}
struct Measurement {float kernel_ms=0;double construction_ms=0,ladder_ms=0,setup_ms=0,kernel_wall_ms=0,download_ms=0,verification_ms=0,cleanup_ms=0;};
static void require_same(const std::vector<uint8_t>& a,const std::vector<uint8_t>& b){if(a!=b){fprintf(stderr,"full table mismatch\n");exit(3);}}
static void table_hash(const std::vector<uint8_t>& a,char out[65]){unsigned char digest[32];QSB_SSL_PTR(SHA256(a.data(),a.size(),digest));for(int i=0;i<32;++i)sprintf(out+2*i,"%02x",digest[i]);out[64]=0;}
static void compare_ladders(const uint8_t scalar[32]){
    std::vector<uint64_t>L(size_t(GT_CHUNKS)*GT_LO*8),H(size_t(GT_CHUNKS)*GT_HI*8),C(L.size()),D(H.size());
    gt_build_ladders(L.data(),H.data(),scalar);batch_ladders(C.data(),D.data(),scalar);
    qsb_ssl_require(L==C&&H==D);size_t padding=0;
    for(int ch=0;ch<GT_CHUNKS;++ch){
        for(int j=0;j<8;++j)qsb_ssl_require(L[size_t(ch)*GT_LO*8+j]==0);++padding;
        for(unsigned i=0;i<GT_HI;++i)if(i==0||i>=(gt_entries(ch)>>7)){
            for(int j=0;j<8;++j)qsb_ssl_require(H[(size_t(ch)*GT_HI+i)*8+j]==0);++padding;
        }
    }
    qsb_ssl_require(padding==7198);
}
static Measurement construct(const uint8_t scalar[32],bool candidate,std::vector<uint8_t>& output){
    Measurement m;double start=wall_ms(),cleanup_begin=0;
    {
        std::vector<uint64_t>L(size_t(GT_CHUNKS)*GT_LO*8),H(size_t(GT_CHUNKS)*GT_HI*8);
        if(candidate)batch_ladders(L.data(),H.data(),scalar);else gt_build_ladders(L.data(),H.data(),scalar);
        double t=wall_ms();m.ladder_ms=t-start;
        uint64_t *dL=nullptr,*dH=nullptr;uint8_t* dt=nullptr;cudaEvent_t a,b;
        CK(cudaMalloc(&dL,L.size()*8));CK(cudaMalloc(&dH,H.size()*8));CK(cudaMalloc(&dt,output.size()));
        CK(cudaMemcpy(dL,L.data(),L.size()*8,cudaMemcpyHostToDevice));CK(cudaMemcpy(dH,H.data(),H.size()*8,cudaMemcpyHostToDevice));
        // Distinct initial bytes detect unwritten slots during full comparison.
        CK(cudaMemset(dt,candidate?0xa5:0x5a,output.size()));CK(cudaDeviceSynchronize());
        CK(cudaEventCreate(&a));CK(cudaEventCreate(&b));double k=wall_ms();m.setup_ms=k-t;
        CK(cudaEventRecord(a));kernel_build_gtable<<<(GT_TOTAL_ENTRIES+255)/256,256>>>(dL,dH,dt);CK(cudaGetLastError());
        CK(cudaEventRecord(b));CK(cudaEventSynchronize(b));CK(cudaEventElapsedTime(&m.kernel_ms,a,b));
        double d=wall_ms();m.kernel_wall_ms=d-k;
        CK(cudaMemcpy(output.data(),dt,output.size(),cudaMemcpyDeviceToHost));double v=wall_ms();m.download_ms=v-d;
        if(!gt_spot_check(output.data(),GT_CHUNKS*4+192,scalar)){fprintf(stderr,"independent table oracle failed\n");exit(4);}
        cleanup_begin=wall_ms();m.verification_ms=cleanup_begin-v;
        CK(cudaEventDestroy(a));CK(cudaEventDestroy(b));CK(cudaFree(dL));CK(cudaFree(dH));CK(cudaFree(dt));
    } // Include host ladder storage destruction in cleanup and whole interval.
    double end=wall_ms();m.cleanup_ms=end-cleanup_begin;m.construction_ms=end-start;return m;
}
int main(int argc,char**argv){
    if(argc!=2&&!(argc==3&&!strcmp(argv[2],"--correctness-only"))){fprintf(stderr,"usage: table-gate OUTPUT.json [--correctness-only]\n");return 1;}
    const bool correctness_only=argc==3;FILE* report=fopen(argv[1],"wx");if(!report){perror("report");return 1;}
    cudaDeviceProp props;CK(cudaGetDeviceProperties(&props,0));CK(cudaSetDevice(0));CK(cudaFree(0));
    std::vector<uint8_t>baseline(size_t(GT_TOTAL_ENTRIES)*64),candidate(baseline.size());
    uint8_t scalars[3][32]={{1},{17},{0}};for(int i=0;i<31;++i)scalars[2][i]=uint8_t(i*7+3);
    char hashes[3][65];
    for(int i=0;i<3;++i){compare_ladders(scalars[i]);construct(scalars[i],false,baseline);construct(scalars[i],true,candidate);require_same(baseline,candidate);table_hash(candidate,hashes[i]);}
    // Every correctness gate completes before any retained timing measurement.
    fprintf(report,"{\"status\":\"passed\",\"geometry\":15,\"records_per_table\":1048576,\"full_tables_compared\":3,\"ladder_records_per_fixture\":19200,\"host_ladder_fixtures_compared\":3,\"openssl_samples_per_table\":252,\"original_kernel_sha256\":\"%s\",\"table_sha256\":[\"%s\",\"%s\",\"%s\"],\"gpu\":\"%s\",\"timingExecuted\":%s,\"samples\":[",ORIGINAL_KERNEL_SHA256,hashes[0],hashes[1],hashes[2],props.name,correctness_only?"false":"true");
    int count=0;
    for(int pair=0;pair<(correctness_only?0:7);++pair){for(int order=0;order<2;++order){bool arm=(pair+order)%2;
        Measurement m=construct(scalars[0],arm,arm?candidate:baseline);
        fprintf(report,"%s{\"pair\":%d,\"order\":%d,\"binary\":\"%s\",\"kernel_ms\":%.6f,\"construction_ms\":%.6f,\"ladder_ms\":%.6f,\"setup_ms\":%.6f,\"kernel_wall_ms\":%.6f,\"download_ms\":%.6f,\"verification_ms\":%.6f,\"cleanup_ms\":%.6f}",count++?",":"",pair,order,arm?"candidate":"baseline",m.kernel_ms,m.construction_ms,m.ladder_ms,m.setup_ms,m.kernel_wall_ms,m.download_ms,m.verification_ms,m.cleanup_ms);
    }require_same(baseline,candidate);}
    fprintf(report,"]}\n");if(ferror(report)||fclose(report)!=0)return 5;
    puts("Host ladder full-table differential and independent OpenSSL samples passed; receipt saved.");return 0;
}
