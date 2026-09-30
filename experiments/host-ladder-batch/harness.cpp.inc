// Fixed public fixtures only. Independent direct multiplication oracle.
static void fixture(unsigned which,uint8_t out[32]) {
    static const char* values[]={"1","2","FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140","8000000000000000000000000000000000000000000000000000000000000000","FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF","0","FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"};
    BIGNUM* b=nullptr; qsb_ssl_require(BN_hex2bn(&b,values[which])>0); QSB_SSL_SIZE(BN_bn2lebinpad(b,out,32),32);BN_free(b);
}
static size_t oracle(const std::vector<uint64_t>& L,const std::vector<uint64_t>& H,const uint8_t scalar[32]) {
    EC_GROUP* g=QSB_SSL_PTR(EC_GROUP_new_by_curve_name(NID_secp256k1));BN_CTX* c=QSB_SSL_PTR(BN_CTX_new());
    BIGNUM *n=QSB_SSL_PTR(BN_new()),*s=QSB_SSL_PTR(BN_lebin2bn(scalar,32,nullptr)),*two=QSB_SSL_PTR(BN_new()),*inv=QSB_SSL_PTR(BN_new()),*k=QSB_SSL_PTR(BN_new()),*x=QSB_SSL_PTR(BN_new()),*y=QSB_SSL_PTR(BN_new());
    EC_POINT* p=QSB_SSL_PTR(EC_POINT_new(g));QSB_SSL_OK(EC_GROUP_get_order(g,n,c));QSB_SSL_OK(BN_set_word(two,2));QSB_SSL_PTR(BN_mod_inverse(inv,two,n,c));QSB_SSL_OK(BN_mod_mul(s,s,inv,n,c));
    size_t checked=0,padding=0;
    for(int ch=0;ch<GT_CHUNKS;++ch) for(int high=0;high<2;++high){
        const auto& table=high?H:L;unsigned width=high?GT_HI:GT_LO,limit=high?(gt_entries(ch)>>7):GT_LO;
        for(unsigned i=0;i<width;++i){const uint64_t* record=&table[(size_t(ch)*width+i)*8];
            if(!i||i>=limit){for(int j=0;j<8;++j)qsb_ssl_require(record[j]==0);++padding;continue;}
            if(i!=1&&i!=limit-1&&i!=limit/2)continue;
            QSB_SSL_OK(BN_set_word(k,i*(high?256:1)));QSB_SSL_OK(BN_lshift(k,k,gt_shift(ch)));QSB_SSL_OK(BN_mod_mul(k,k,s,n,c));
            QSB_SSL_OK(EC_POINT_mul(g,p,k,nullptr,nullptr,c));
            // Separate serialization from the shared baseline export helper.
            QSB_SSL_OK(EC_POINT_get_affine_coordinates(g,p,x,y,c));uint8_t expected[64];QSB_SSL_SIZE(BN_bn2lebinpad(x,expected,32),32);QSB_SSL_SIZE(BN_bn2lebinpad(y,expected+32,32),32);
            qsb_ssl_require(memcmp(expected,record,64)==0);++checked;
        }
    }
    qsb_ssl_require(padding==7198&&checked==90);
    EC_POINT_free(p);EC_GROUP_free(g);BN_CTX_free(c);BN_free(n);BN_free(s);BN_free(two);BN_free(inv);BN_free(k);BN_free(x);BN_free(y);return checked;
}
int main(int argc,char**argv){
    if(argc!=2){fprintf(stderr,"usage: host-ladder-gate OUTPUT.json (fixed public fixtures only)\n");return 1;}
    std::vector<uint64_t> L(size_t(GT_CHUNKS)*GT_LO*8),H(size_t(GT_CHUNKS)*GT_HI*8),C(L.size()),D(H.size());
    // Test-only modes have no arbitrary scalar input and preserve baseline rejection.
    const char* modes[]={"--reject-baseline-zero","--reject-batch-zero","--reject-baseline-order","--reject-batch-order"};
    for(unsigned i=0;i<4;++i)if(!strcmp(argv[1],modes[i])){uint8_t s[32];fixture(5+i/2,s);if(i%2)batch_ladders(C.data(),D.data(),s);else gt_build_ladders(L.data(),H.data(),s);return 3;}
    FILE* f=fopen(argv[1],"wx");if(!f)return 1;
    fprintf(f,"{\"schema\":1,\"scope\":\"public-point-ladder-only\",\"openssl\":\"%s\",\"records_per_fixture\":19200,\"populated_per_fixture\":12002,\"padding_per_fixture\":7198,\"samples_per_fixture\":90,\"fixtures\":[",OpenSSL_version(OPENSSL_VERSION));
    for(unsigned i=0;i<5;++i){uint8_t s[32];fixture(i,s);
        auto a=std::chrono::steady_clock::now();gt_build_ladders(L.data(),H.data(),s);auto b=std::chrono::steady_clock::now();batch_ladders(C.data(),D.data(),s);auto d=std::chrono::steady_clock::now();
        qsb_ssl_require(L==C&&H==D);oracle(C,D,s);
        fprintf(f,"%s{\"public_fixture\":%u,\"all_records_equal\":true,\"baseline_ms\":%.6f,\"batch_ms\":%.6f}",i?",":"",i,std::chrono::duration<double,std::milli>(b-a).count(),std::chrono::duration<double,std::milli>(d-b).count());
    }
    fprintf(f,"],\"status\":\"passed\",\"timing\":\"single-pair-local-diagnostic-not-A10G-or-solver-speedup\"}\n");qsb_ssl_require(ferror(f)==0);qsb_ssl_require(fclose(f)==0);return 0;
}
