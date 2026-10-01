// Fixed public scalar1 tables only: no transaction, wallet, recovery or search.
#include <unistd.h>
#include <array>
#define CK(call) do{cudaError_t e=(call);if(e!=cudaSuccess){fprintf(stderr,"CUDA %s:%d %s\n",__FILE__,__LINE__,cudaGetErrorString(e));exit(2);}}while(0)
static double now_ms(){return std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now().time_since_epoch()).count();}
struct Row{double construction_ms=0,ladder_ms=0,allocate_ms=0,upload_ms=0,kernel_wall_ms=0,download_ms=0,verification_ms=0,cleanup_ms=0,hash_ms=0;float kernel_ms=0;};
static Row construct(bool candidate,std::vector<uint8_t>& output){
    const uint8_t scalar[32]={1};Row row;double start=now_ms(),cleanup_begin=0;
    {
        std::vector<uint64_t>L(size_t(GT_CHUNKS)*GT_LO*8),H(size_t(GT_CHUNKS)*GT_HI*8);
        if(candidate)batch_ladders(L.data(),H.data(),scalar);else gt_build_ladders(L.data(),H.data(),scalar);
        double allocated_begin=now_ms();row.ladder_ms=allocated_begin-start;
        uint64_t *dL=nullptr,*dH=nullptr;uint8_t* dt=nullptr;cudaEvent_t a,b;
        CK(cudaMalloc(&dL,L.size()*8));CK(cudaMalloc(&dH,H.size()*8));CK(cudaMalloc(&dt,output.size()));CK(cudaEventCreate(&a));CK(cudaEventCreate(&b));
        double upload_begin=now_ms();row.allocate_ms=upload_begin-allocated_begin;
        CK(cudaMemcpy(dL,L.data(),L.size()*8,cudaMemcpyHostToDevice));CK(cudaMemcpy(dH,H.data(),H.size()*8,cudaMemcpyHostToDevice));
        CK(cudaMemset(dt,candidate?0xa5:0x5a,output.size()));CK(cudaDeviceSynchronize());
        double kernel_begin=now_ms();row.upload_ms=kernel_begin-upload_begin;
        CK(cudaEventRecord(a));kernel_build_gtable<<<(GT_TOTAL_ENTRIES+255)/256,256>>>(dL,dH,dt);CK(cudaGetLastError());CK(cudaEventRecord(b));CK(cudaEventSynchronize(b));CK(cudaEventElapsedTime(&row.kernel_ms,a,b));
        double download_begin=now_ms();row.kernel_wall_ms=download_begin-kernel_begin;
        CK(cudaMemcpy(output.data(),dt,output.size(),cudaMemcpyDeviceToHost));double verify_begin=now_ms();row.download_ms=verify_begin-download_begin;
        if(!gt_spot_check(output.data(),252,scalar)){fprintf(stderr,"independent public table oracle failed\n");exit(3);}
        cleanup_begin=now_ms();row.verification_ms=cleanup_begin-verify_begin;
        CK(cudaEventDestroy(a));CK(cudaEventDestroy(b));CK(cudaFree(dL));CK(cudaFree(dH));CK(cudaFree(dt));
    }
    double end=now_ms();row.cleanup_ms=end-cleanup_begin;row.construction_ms=end-start;return row;
}
static void digest_table(const std::vector<uint8_t>& table,char hex[65]){
    unsigned char digest[32];QSB_SSL_PTR(SHA256(table.data(),table.size(),digest));for(int i=0;i<32;++i)sprintf(hex+2*i,"%02x",digest[i]);hex[64]=0;
}
int main(int argc,char** argv){
    const double begin=now_ms();
    if(argc!=4||(strcmp(argv[2],"baseline")&&strcmp(argv[2],"candidate"))||(strcmp(argv[3],"1")&&strcmp(argv[3],"4")&&strcmp(argv[3],"16"))){fprintf(stderr,"usage: table-gate OUTPUT.json baseline|candidate 1|4|16\n");return 1;}
    const bool candidate=!strcmp(argv[2],"candidate");const int repetitions=atoi(argv[3]);
    FILE* report=fopen(argv[1],"wx");if(!report){perror("exclusive report");return 1;}
    std::array<Row,16> rows;std::array<std::array<char,65>,16> hashes;
    const double context_begin=now_ms();cudaDeviceProp props;CK(cudaGetDeviceProperties(&props,0));CK(cudaSetDevice(0));CK(cudaFree(0));
    const double context_end=now_ms(),context_init_ms=context_end-context_begin;
    double output_allocation_ms=0,output_cleanup_ms=0;
    {
        const double allocation_begin=now_ms();std::vector<uint8_t> output(size_t(GT_TOTAL_ENTRIES)*64);output_allocation_ms=now_ms()-allocation_begin;
        for(int i=0;i<repetitions;++i){rows[i]=construct(candidate,output);const double hash_begin=now_ms();digest_table(output,hashes[i].data());rows[i].hash_ms=now_ms()-hash_begin;
            if(strcmp(hashes[i].data(),EXPECTED_TABLE_SHA256)){fprintf(stderr,"fixed public table SHA256 mismatch\n");return 4;}}
        output_cleanup_ms=now_ms();
    }
    output_cleanup_ms=now_ms()-output_cleanup_ms;
    const double before_report_elapsed_ms=now_ms()-begin;
    fprintf(report,"{\"schema\":1,\"status\":\"passed\",\"noSolverSearch\":true,\"arm\":\"%s\",\"repetitions\":%d,\"public_scalar\":1,\"geometry\":15,\"records_per_table\":1048576,\"openssl_samples_per_table\":252,\"table_sha256\":\"%s\",\"expected_table_sha256\":\"%s\",\"original_kernel_sha256\":\"%s\",\"gpu\":\"%s\",\"context_init_ms\":%.6f,\"output_allocation_ms\":%.6f,\"output_cleanup_ms\":%.6f,\"before_report_elapsed_ms\":%.6f,\"tables\":[",argv[2],repetitions,EXPECTED_TABLE_SHA256,EXPECTED_TABLE_SHA256,ORIGINAL_KERNEL_SHA256,props.name,context_init_ms,output_allocation_ms,output_cleanup_ms,before_report_elapsed_ms);
    for(int i=0;i<repetitions;++i){const Row&r=rows[i];fprintf(report,"%s{\"index\":%d,\"table_sha256\":\"%s\",\"construction_ms\":%.6f,\"ladder_ms\":%.6f,\"allocate_ms\":%.6f,\"upload_ms\":%.6f,\"kernel_ms\":%.6f,\"kernel_wall_ms\":%.6f,\"download_ms\":%.6f,\"verification_ms\":%.6f,\"cleanup_ms\":%.6f,\"hash_ms\":%.6f}",i?",":"",i,hashes[i].data(),r.construction_ms,r.ladder_ms,r.allocate_ms,r.upload_ms,r.kernel_ms,r.kernel_wall_ms,r.download_ms,r.verification_ms,r.cleanup_ms,r.hash_ms);}
    fprintf(report,"]}\n");if(ferror(report)||fflush(report)!=0){fclose(report);return 5;}if(fsync(fileno(report))!=0){fclose(report);return 5;}if(fclose(report)!=0)return 5;
    puts("Synthetic public table subprocess completed; receipt saved.");return 0;
}
