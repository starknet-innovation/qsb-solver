// Independently implemented public point recurrence with owned snapshots.
// Experiment only: deprecated EC_POINTs_make_affine has no OpenSSL 3 replacement.
static void batch_ladders(uint64_t* L, uint64_t* H, const uint8_t scalar[32]) {
    EC_GROUP* g=QSB_SSL_PTR(EC_GROUP_new_by_curve_name(NID_secp256k1));
    BN_CTX* ctx=QSB_SSL_PTR(BN_CTX_new());
    BIGNUM *n=QSB_SSL_PTR(BN_new()), *s=QSB_SSL_PTR(BN_lebin2bn(scalar,32,nullptr)),
      *two=QSB_SSL_PTR(BN_new()), *half=QSB_SSL_PTR(BN_new()), *factor=QSB_SSL_PTR(BN_new()),
      *x=QSB_SSL_PTR(BN_new()), *y=QSB_SSL_PTR(BN_new());
    QSB_SSL_OK(EC_GROUP_get_order(g,n,ctx)); QSB_SSL_OK(BN_set_word(two,2));
    QSB_SSL_PTR(BN_mod_inverse(half,two,n,ctx)); QSB_SSL_OK(BN_mod_mul(s,s,half,n,ctx));
    EC_POINT *base=QSB_SSL_PTR(EC_POINT_new(g)), *step=QSB_SSL_PTR(EC_POINT_new(g)), *acc=QSB_SSL_PTR(EC_POINT_new(g));
    QSB_SSL_OK(EC_POINT_mul(g,base,s,nullptr,nullptr,ctx));
    memset(L,0,size_t(GT_CHUNKS)*GT_LO*64); memset(H,0,size_t(GT_CHUNKS)*GT_HI*64);
    std::vector<EC_POINT*> points; std::vector<uint64_t*> destinations;
    auto retain=[&](uint64_t* dst){
        EC_POINT* owned=QSB_SSL_PTR(EC_POINT_new(g));
        QSB_SSL_OK(EC_POINT_copy(owned,acc)); points.push_back(owned); destinations.push_back(dst);
    };
    for(int ch=0;ch<GT_CHUNKS;++ch){
        if(ch){QSB_SSL_OK(BN_set_word(factor,1ul<<(gt_shift(ch)-gt_shift(ch-1)))); QSB_SSL_OK(EC_POINT_mul(g,base,nullptr,base,factor,ctx));}
        QSB_SSL_OK(EC_POINT_copy(acc,base));
        for(int i=1;i<GT_LO;++i){retain(L+(size_t(ch)*GT_LO+i)*8);QSB_SSL_OK(EC_POINT_add(g,acc,acc,base,ctx));}
        QSB_SSL_OK(BN_set_word(factor,256));QSB_SSL_OK(EC_POINT_mul(g,step,nullptr,base,factor,ctx));
        QSB_SSL_OK(EC_POINT_copy(acc,step));
        for(unsigned i=1;i<(gt_entries(ch)>>7);++i){retain(H+(size_t(ch)*GT_HI+i)*8);QSB_SSL_OK(EC_POINT_add(g,acc,acc,step,ctx));}
    }
    QSB_SSL_OK(EC_POINTs_make_affine(g,points.size(),points.data(),ctx));
    for(size_t i=0;i<points.size();++i){gt_point_to_limbs(g,points[i],x,y,ctx,destinations[i]);EC_POINT_free(points[i]);}
    EC_POINT_free(base);EC_POINT_free(step);EC_POINT_free(acc);
    BN_free(n);BN_free(s);BN_free(two);BN_free(half);BN_free(factor);BN_free(x);BN_free(y);BN_CTX_free(ctx);EC_GROUP_free(g);
}
