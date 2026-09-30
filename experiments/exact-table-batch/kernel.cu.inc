/* Independent experiment: exact Montgomery batching with existing field math.
 * No new point formulas or scalar representation. Exactly 256 threads/block.
 * All lanes participate in the warp product tree, including copy/padding lanes.
 */
__global__ void kernel_build_gtable(
    const uint64_t * __restrict__ d_L,
    const uint64_t * __restrict__ d_H,
    uint8_t * __restrict__ gTable)
{
    if (blockDim.x != 256 || blockDim.y != 1 || blockDim.z != 1) {
        asm volatile("trap;"); return;
    }
    __shared__ uint64_t product[8][64][4];
    const int lane = threadIdx.x & 31, warp = threadIdx.x >> 5;
    const uint64_t t = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const bool active = t < GT_TOTAL_ENTRIES;
    uint64_t px[4] = {0}, py[4] = {0}, pz[5] = {1,0,0,0,0};
    bool copy = true;
    if (active) {
#if ZLAB_T14
        int ch=t<((uint64_t)GT_BIG<<18)?(int)(t>>18):GT_BIG+(int)((t-((uint64_t)GT_BIG<<18))>>17);
#else
        int ch=t<(1u<<17)?0:1+(int)((t-(1u<<17))>>16);
#endif
        int d=(int)(t-gt_offset(ch));
        int m=2*d+1, hi=m>>8, lo=m&255;
        const uint64_t *Hp=d_H+((size_t)ch*GT_HI+hi)*8;
        const uint64_t *Lp=d_L+((size_t)ch*GT_LO+lo)*8;
        copy = hi == 0;
        if (copy) {
            for (int k=0;k<4;k++) { px[k]=Lp[k]; py[k]=Lp[4+k]; }
        } else {
            uint64_t qx[4], qy[4];
            for (int k=0;k<4;k++) {
                px[k]=Hp[k]; py[k]=Hp[4+k]; qx[k]=Lp[k]; qy[k]=Lp[4+k];
            }
            _PointAddSecp256k1(px,py,pz,qx,qy);
        }
    }
    // A zero denominator takes the original per-record inversion path. It must
    // not zero the product and corrupt unrelated records in this warp.
    const bool zero = (pz[0]|pz[1]|pz[2]|pz[3]) == 0 ||
        (pz[0]==UINT64_C(0xfffffffefffffc2f) && pz[1]==UINT64_MAX &&
         pz[2]==UINT64_MAX && pz[3]==UINT64_MAX);
    for (int k=0;k<4;k++) product[warp][32+lane][k] = zero ? (k==0) : pz[k];
    __syncwarp();
    for (int count=16;count;count>>=1) {
        if (lane<count) {
            int node=count+lane;
            uint64_t a[4],b[4];
            for (int k=0;k<4;k++) { a[k]=product[warp][2*node][k]; b[k]=product[warp][2*node+1][k]; }
            _ModMult(a,b);
            for (int k=0;k<4;k++) product[warp][node][k]=a[k];
        }
        __syncwarp();
    }
    if (lane==0) {
        uint64_t inverse[5]={0,0,0,0,0};
        for (int k=0;k<4;k++) inverse[k]=product[warp][1][k];
        _ModInv(inverse);
        for (int k=0;k<4;k++) product[warp][1][k]=inverse[k];
    }
    __syncwarp();
    for (int count=1;count<=16;count<<=1) {
        if (lane<count) {
            int node=count+lane;
            uint64_t inv[4],left[4],right[4];
            for (int k=0;k<4;k++) {
                inv[k]=product[warp][node][k];
                left[k]=product[warp][2*node][k]; right[k]=product[warp][2*node+1][k];
            }
            _ModMult(left,inv); _ModMult(right,inv);
            for (int k=0;k<4;k++) {
                product[warp][2*node][k]=right[k]; product[warp][2*node+1][k]=left[k];
            }
        }
        __syncwarp();
    }
    if (active && !copy) {
        uint64_t inv[5]={0,0,0,0,0},check[4];
        for (int k=0;k<4;k++) { inv[k]=product[warp][32+lane][k]; check[k]=pz[k]; }
        _ModMult(check,inv);
        const bool canonical = inv[3]!=UINT64_MAX || inv[2]!=UINT64_MAX ||
            inv[1]!=UINT64_MAX || inv[0]<UINT64_C(0xfffffffefffffc2f);
        if (zero || !canonical || check[0]!=1 || check[1] || check[2] || check[3]) {
            // Exact original behavior, including _ModInv(0), not an omission.
            _ModInv(pz);
        } else {
            for (int k=0;k<4;k++) pz[k]=inv[k];
        }
        _ModMult(px,pz); _ModMult(py,pz);
    }
    if (active) {
        memcpy(gTable+t*64,px,32); memcpy(gTable+t*64+32,py,32);
    }
}
