// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// CUDA grinder (see README.md). Per batch, on one of two non-blocking CUDA streams (two batches in flight):
//   zgen_pin : (pin) one thread per z-block over a precomputed midstate
//   zpre     : (round) persistent lanes: a uniform (t-1)-prefix per item, a full sweep of its
//              completions; emits each subset's midstate after its boundary block (nz decided on
//              the GPU: budget <= nz < budget + ZSLACK, read by later kernels from ctr[2])
//   ztail    : (round) persistent lanes hash each subset's tail (region T) + the outer SHA-256
//   ec_comb  : one thread per ZB z-blocks: W = z*B (16-bit comb, 64 MiB table, Jacobian mixed
//              adds), Z's batch-inverted -> affine W, then prefix products of the menu
//              denominators D = x_C - x_W and ONE more inversion (safegcd)
//   ec_menu  : the back pass: Q = W + C[j][rid] in affine, a +-R recid pair shares a denominator;
//              QG_FUSE (default): hashes each point in registers (SHA-256 -> gate -> hits)
//   hash_pts : (QG_FUSE=0 only) one thread per (point, encoding): SHA-256 -> gate -> hits
//
//   grind --problem P.json --hits hits.txt --seconds S     (reads P.txt next to P.json)
//
// The three PQB track shapes are template instances (nvcc compiles once, before the problem is
// known). Profiling: prints @setup/@batch/@done; -DQG_STAGE=k cuts after stage k and skips the
// later kernels. -DQG_EMU builds the same code as plain C++ that runs every kernel
// on the CPU, for validating without an NVIDIA GPU.
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <sstream>
#include <string>
#include <thread>
#include <vector>
#include <unistd.h>
#include "common.cuh"
#include "ptx_field.cuh"                          // CUDA: field ops as PTX carry chains (generated)

#ifndef QG_STAGE
#define QG_STAGE 99
#endif

#ifndef QG_ZB
#define QG_ZB 4
#endif
#ifndef QG_TPB
#define QG_TPB 128
#endif
#ifndef QG_NSLOT
#define QG_NSLOT 2
#endif
#ifndef QG_NCONN                                   // hardware work queues (CUDA_DEVICE_MAX_CONNECTIONS)
#define QG_NCONN QG_NSLOT
#endif
#ifndef QG_FUSE                                    // 1: ec_menu hashes its points (no pts buffer, no hash_pts)
#define QG_FUSE 1
#endif
#ifndef QG_LB_COMB                                  // __launch_bounds__ min blocks per SM (0: none)
#define QG_LB_COMB 0
#endif
#ifndef QG_LB_MENU
#define QG_LB_MENU 0
#endif
static const uint ZB = QG_ZB;                      // z-blocks per ec thread (one inversion)
#ifndef QG_LANES
#define QG_LANES 65536
#endif
static const uint LANES = QG_LANES;                // round: persistent zpre / ztail lanes
static const uint ZSLACK = 128;                    // round: a batch may overrun its budget by < c_max
static const uint HIT_CAP = 1u << 20;

// ------------------------------------------------------------------------------ backend shim
#if defined(__CUDACC__) && !defined(QG_EMU)
#define KERNEL __global__ void
#define GID (blockIdx.x * blockDim.x + threadIdx.x)
#define QG_CMEM __constant__
QG_FI uint atom_add(uint *p, uint v) { return atomicAdd(p, v); }
QG_FI uint atom_max(uint *p, uint v) { return atomicMax(p, v); }
QG_FI uint qg_clz(uint x) { return (uint)__clz((int)x); }
#else
struct uint4 { uint x, y, z, w; };
static inline uint4 make_uint4(uint x, uint y, uint z, uint w) { return uint4{x, y, z, w}; }
static thread_local uint qg_gid;
#define KERNEL static void
#define GID qg_gid
#define QG_CMEM static
static inline uint atom_add(uint *p, uint v) { return __atomic_fetch_add(p, v, __ATOMIC_RELAXED); }
static inline uint atom_max(uint *p, uint v) { uint o = __atomic_load_n(p, __ATOMIC_RELAXED); while (o < v && !__atomic_compare_exchange_n(p, &o, v, true, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {} return o; }
static inline uint qg_clz(uint x) { return (uint)__builtin_clz(x); }
#endif
QG_FI uint qg_min(uint a, uint b) { return a < b ? a : b; }
QG_FI uint qg_max(uint a, uint b) { return a > b ? a : b; }
QG_FI uint qg_rotl(uint x, uint n) { return (x << n) | (x >> (32 - n)); }

struct Hit { uint a, b, c, d; };                   // c = j | recid<<8 | enc<<16 | lvl<<24
QG_CMEM ge c_cpts[64];                             // C[j][recid] at j * npts + recid
QG_CMEM uint c_gate[2];                            // gate_bits, tag

// ------------------------------------------------------------------------------ group law
QG_FI gej gej_add_ge(gej p, ge q) {                // p (Jacobian, not infinity) + q (affine), p != +-q
    fe z1z1 = fe_sqr(p.z);
    fe u2 = fe_mul(q.x, z1z1);
    fe s2 = fe_mul(fe_mul(q.y, p.z), z1z1);
    fe h = fe_sub(u2, p.x);
    fe rr = fe_sub(s2, p.y);
    fe hh = fe_sqr(h);
    fe hhh = fe_mul(h, hh);
    fe v = fe_mul(p.x, hh);
    gej r;
    r.x = fe_sub(fe_sub(fe_sqr(rr), hhh), fe_dbl(v));
    r.y = fe_sub(fe_mul(rr, fe_sub(v, r.x)), fe_mul(p.y, hhh));
    r.z = fe_mul(p.z, h);
    return r;
}

QG_FI gej gej_double(gej p) {                      // dbl-2009-l (a = 0), p not infinity
    fe A = fe_sqr(p.x), B = fe_sqr(p.y), C = fe_sqr(B);
    fe D = fe_dbl(fe_sub(fe_sub(fe_sqr(fe_add(p.x, B)), A), C));
    fe E = fe_add(fe_dbl(A), A);
    gej r;
    r.x = fe_sub(fe_sqr(E), fe_dbl(D));
    fe C8 = fe_dbl(fe_dbl(fe_dbl(C)));
    r.y = fe_sub(fe_mul(E, fe_sub(D, r.x)), C8);
    r.z = fe_dbl(fe_mul(p.y, p.z));
    return r;
}

// Comb table, 16-bit windows: table[w*65536 + d] = d * 2^(16w) * B (entry 0 unused), 64 MiB.
// One thread per (window, chunk of 64): double-and-add to the chunk start, sequential adds, one
// batch inversion for the chunk (Z and prefix products in zq / zz scratch).
#define TB_CHUNK 64u
KERNEL build_table(ge *table, const ge *bases, fe *zq, fe *zz) {
    uint tid = GID;
    if (tid >= 16 * (65536 / TB_CHUNK)) return;
    uint w = tid / (65536 / TB_CHUNK), c = tid % (65536 / TB_CHUNK);
    ge base = bases[w];
    uint lo = qg_max(c * TB_CHUNK, 1u), hi = c * TB_CHUNK + TB_CHUNK;
    gej acc; acc.x = base.x; acc.y = base.y; acc.z = fe_one();
    int top = 31 - (int)qg_clz(lo);
    for (int bit = top - 1; bit >= 0; bit--) {
        acc = gej_double(acc);
        if ((lo >> bit) & 1u) acc = gej_add_ge(acc, base);
    }
    uint o = w * 65536;
    fe q = fe_one();
    for (uint d = lo; d < hi; d++) {
        if (d > lo) acc = (d == 2) ? gej_double(acc) : gej_add_ge(acc, base);
        q = (d == lo) ? acc.z : fe_mul(q, acc.z);
        zq[o + d] = q; zz[o + d] = acc.z;
        table[o + d].x = acc.x; table[o + d].y = acc.y;
    }
    fe inv = fe_inv(q);
    for (uint d = hi - 1; ; d--) {
        fe zi = (d > lo) ? fe_mul(inv, zq[o + d - 1]) : inv;
        if (d > lo) inv = fe_mul(inv, zz[o + d]);
        fe zi2 = fe_sqr(zi);
        ge r;
        r.x = fe_norm(fe_mul(table[o + d].x, zi2));
        r.y = fe_norm(fe_mul(table[o + d].y, fe_mul(zi2, zi)));
        table[o + d] = r;
        if (d == lo) break;
    }
}

// ------------------------------------------------------------------------------ SHA helpers
QG_FI bool gate(uint w0) {
    uint sh = 32 - c_gate[0];
    return (w0 >> sh) == (c_gate[1] >> sh);
}

QG_FI shst sha_of_digest(shst d) {
    return sha_blk(SHA_IV, d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
                   0x80000000u, 0u, 0u, 0u, 0u, 0u, 0u, 256u);
}

QG_FI void emit(uint *count, Hit *hits, uint4 id, uint c) {
    uint i = atom_add(count, 1u);
    if (i < HIT_CAP) { hits[i].a = id.x; hits[i].b = id.y; hits[i].c = c; hits[i].d = id.z; }
}

// All NE encodings of one point, straight from registers (QG_FUSE: ec_menu hashes, no pts buffer)
template <int NP, int NE, int H>
QG_FI void hash_point(fe x, fe y, uint jr, uint zi, const uint4 *zinfo, uint *count, Hit *hits) {
    x = fe_norm(x); y = fe_norm(y);
#if QG_STAGE == 5                                    // profiling cut: points only
    if ((x.v0 ^ y.v1) == 0x9E3779B9u) atom_add(count, 1u);
    return;
#endif
    uint x0 = x.v7, x1 = x.v6, x2 = x.v5, x3 = x.v4, x4 = x.v3, x5 = x.v2, x6 = x.v1, x7 = x.v0;
    uint y0 = y.v7, y1 = y.v6, y2 = y.v5, y3 = y.v4, y4 = y.v3, y5 = y.v2, y6 = y.v1, y7 = y.v0;
    uint c = (jr / NP) | ((jr % NP) << 8);
#pragma unroll
    for (int e = 0; e < (QG_STAGE == 6 ? 1 : NE); e++) {     // cut 6: compressed only
        shst s;
        if (e == 0) {
            s = sha_blk(SHA_IV, 0x02000000u | ((y7 & 1u) << 24) | (x0 >> 8), (x0 << 24) | (x1 >> 8), (x1 << 24) | (x2 >> 8),
                        (x2 << 24) | (x3 >> 8), (x3 << 24) | (x4 >> 8), (x4 << 24) | (x5 >> 8), (x5 << 24) | (x6 >> 8),
                        (x6 << 24) | (x7 >> 8), (x7 << 24) | 0x00800000u, 0u, 0u, 0u, 0u, 0u, 0u, 264u);
        } else {
            uint pfx = e == 1 ? 0x04000000u : (0x06000000u | ((y7 & 1u) << 24));
            s = sha_blk(SHA_IV, pfx | (x0 >> 8), (x0 << 24) | (x1 >> 8), (x1 << 24) | (x2 >> 8),
                        (x2 << 24) | (x3 >> 8), (x3 << 24) | (x4 >> 8), (x4 << 24) | (x5 >> 8), (x5 << 24) | (x6 >> 8),
                        (x6 << 24) | (x7 >> 8), (x7 << 24) | (y0 >> 8), (y0 << 24) | (y1 >> 8), (y1 << 24) | (y2 >> 8),
                        (y2 << 24) | (y3 >> 8), (y3 << 24) | (y4 >> 8), (y4 << 24) | (y5 >> 8), (y5 << 24) | (y6 >> 8),
                        (y6 << 24) | (y7 >> 8));
            s = sha_blk(s, (y7 << 24) | 0x00800000u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 520u);
        }
#if QG_STAGE == 6 || QG_STAGE == 7
        if (s.a == 0x9E3779B9u) atom_add(count, 1u);
        continue;
#endif
        uint ce = c | ((uint)e << 16);
        if (gate(s.a)) emit(count, hits, zinfo[zi], ce | (1u << 24));
        for (uint lvl = 2; lvl <= (uint)H; lvl++) {
            s = sha_of_digest(s);
            if (gate(s.a)) emit(count, hits, zinfo[zi], ce | (lvl << 24));
        }
    }
}

// ------------------------------------------------------------------------------ z generation
// zinfo[z]: pin (seq, lt, 0, 0); round the sorted subset as bytes over (x, y, z); x == ~0: unused.
struct PinParams {
    uint mid[8];          // SHA-256 state after the fixed block-aligned prefix
    uint tail[32];        // the remaining bytes, exactly padded, big-endian words (nblk blocks)
    uint seq, lt_base, seq_pos, lt_pos, nblk;
};

QG_FI void put_le32(uint *words, uint pos, uint v) {
    for (uint k = 0; k < 4; k++) {
        uint q = pos + k, sh = 24 - 8 * (q & 3);
        words[q >> 2] = (words[q >> 2] & ~(0xFFu << sh)) | (((v >> (8 * k)) & 0xFFu) << sh);
    }
}

KERNEL zgen_pin(PinParams pp, uint *zbuf, uint4 *zinfo, uint nz) {
    uint gid = GID;
    if (gid >= nz) return;
    uint lt = pp.lt_base + gid;
    uint w[32];
    for (int i = 0; i < 32; i++) w[i] = pp.tail[i];
    put_le32(w, pp.seq_pos, pp.seq);
    put_le32(w, pp.lt_pos, lt);
    shst s; s.a = pp.mid[0]; s.b = pp.mid[1]; s.c = pp.mid[2]; s.d = pp.mid[3];
    s.e = pp.mid[4]; s.f = pp.mid[5]; s.g = pp.mid[6]; s.h = pp.mid[7];
    s = sha_blk(s, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]);
    if (pp.nblk == 2)
        s = sha_blk(s, w[16], w[17], w[18], w[19], w[20], w[21], w[22], w[23], w[24], w[25], w[26], w[27], w[28], w[29], w[30], w[31]);
    s = sha_of_digest(s);
    uint4 *zo = (uint4 *)(zbuf + gid * 8);
    zo[0] = make_uint4(s.a, s.b, s.c, s.d); zo[1] = make_uint4(s.e, s.f, s.g, s.h);
    zinfo[gid] = make_uint4(pp.seq, lt, 0u, 0u);
}

QG_FI qg_u64 splitmix(qg_u64 &s) {
    s += 0x9E3779B97F4A7C15ull;
    qg_u64 z = s;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

QG_FI uint xoshiro(uint4 &s) {                     // xoshiro128**, 32-bit ops only
    uint r = qg_rotl(s.y * 5u, 7u) * 9u, t = s.y << 9;
    s.z ^= s.x; s.w ^= s.y; s.y ^= s.z; s.x ^= s.w; s.z ^= t; s.w = qg_rotl(s.w, 11u);
    return r;
}

// Round z-blocks: a FULL SWEEP of all completions i_t of a uniformly drawn (t-1)-prefix, so every
// t-subset is covered with equal probability. Two kernels:
//   zpre : persistent lanes pull items (a prefix, drawn from the item index), reserve c z-block
//          slots with one atomic (an item is dropped iff its reservation starts past the budget,
//          which depends only on OTHER items: no bias), and run the (t-1)-deleted chain from the
//          first deletion's block; at each completion's boundary block they hash that block with
//          the extra deletion and emit the state after it (the subset's midstate) + next block.
//   ztail: persistent lanes pull z-blocks and hash the rest of the stream (region T only: no
//          boundaries, warp-coherent), then SHA256 of the digest -> z.
// ctr: [0] items pulled, [1] slots reserved, [2] accepted z-blocks (= nz of the batch), [3] ztail
struct RoundGeo { uint nslots, slen, nblk, rwn; };

// Stream words: rw[r * rwn + m] = big-endian word at extended preimage byte 4m + L*r, region
// r = 0..T (+1 spare so the branch-free merge may read region k + 1). A word a boundary cuts at
// byte q in 1..3 takes bytes [0, q) from region k and the rest from region k+1.
template <int T>
QG_FI void stream_block(uint *w, const uint *rw, uint rwn, uint o, const uint *sk) {
    uint k0 = 0, nb = 0xFFFFFFFFu, n2 = 0xFFFFFFFFu, n3 = 0xFFFFFFFFu;   // deletions <= o; next 3 after o
#pragma unroll
    for (int d = 0; d < T; d++) {
        uint v = sk[d];
        k0 += (v <= o) ? 1u : 0u;
        bool g = v > o;                               // sk ascending: the first three > o, in order
        n3 = (g && v < n3) ? qg_max(v, n2) : n3;
        n2 = (g && v < n2) ? qg_max(v, nb) : n2;
        nb = (g && v < nb) ? v : nb;
    }
    const uint *src = rw + k0 * rwn + (o >> 2);
#pragma unroll
    for (int i = 0; i < 16; i++) {                    // <= 3 boundaries per block (>= 22 B apart)
        uint p = o + 4 * i;
        uint k = ((nb <= p) ? 1u : 0u) + ((n2 <= p) ? 1u : 0u) + ((n3 <= p) ? 1u : 0u);
        uint cut = (nb - p - 1 < 3u) ? nb - p : (n2 - p - 1 < 3u) ? n2 - p : (n3 - p - 1 < 3u) ? n3 - p : 4u;
        uint v1 = src[k * rwn + i], v2 = src[(k + 1) * rwn + i];
        uint msk = (uint)(0xFFFFFFFFull << (8 * (4 - cut)));
        w[i] = (v1 & msk) | (v2 & ~msk);
    }
}

template <int T>
KERNEL zpre(qg_u64 seed, uint budget, RoundGeo g, uint *zbuf, uint4 *zinfo, uint *ctr,
            const uint *rw, const uint *soff, const uint *mids) {
    uint sk[T];
    uint px = 0, py = 0, c = 0, k = 0, zs = 0, cb = 0, nsl = 0, il = 0;
    shst A = SHA_IV;
    bool need = true;
    for (;;) {
        if (need) {
            uint item = atom_add(&ctr[0], 1u);
            qg_u64 rs = seed ^ ((qg_u64)item * 0xD6E8FEB86659FD93ull);
            qg_u64 a = splitmix(rs), b = splitmix(rs);
            uint4 x = make_uint4((uint)a, (uint)(a >> 32), (uint)b, (uint)(b >> 32) | 1u);
            uint idx[T - 1];
            for (int i = 0; i < T - 1; i++) {         // uniform (t-1)-subset of [0, n-1): c >= 1
                uint v; bool ok;
                do {
                    v = qg_mulhi(xoshiro(x), g.nslots - 1);
                    ok = true;
                    for (int j = 0; j < i; j++) ok = ok && (idx[j] != v);
                } while (!ok);
                idx[i] = v;
            }
            for (int i = 1; i < T - 1; i++)
                for (int j = i; j > 0 && idx[j - 1] > idx[j]; j--) { uint t = idx[j]; idx[j] = idx[j - 1]; idx[j - 1] = t; }
            il = idx[T - 2];
            c = g.nslots - 1 - il;
            zs = atom_add(&ctr[1], c);
            if (zs >= budget) break;
            atom_max(&ctr[2], zs + c);
            px = 0; py = 0;
#pragma unroll
            for (int i = 0; i < T - 1; i++) {
                sk[i] = soff[idx[i]] - g.slen * i;
                if (i < 4) px |= idx[i] << (8 * i); else py |= idx[i] << (8 * (i - 4));
            }
            cb = sk[0] / 64;                          // blocks before the first deletion: precomputed
            A.a = mids[cb * 8 + 0]; A.b = mids[cb * 8 + 1]; A.c = mids[cb * 8 + 2]; A.d = mids[cb * 8 + 3];
            A.e = mids[cb * 8 + 4]; A.f = mids[cb * 8 + 5]; A.g = mids[cb * 8 + 6]; A.h = mids[cb * 8 + 7];
            k = 0;
            nsl = soff[il + 1] - g.slen * (T - 1);
            need = false;
        }
        bool comp = (nsl >> 6) == cb;                 // this block holds completion k's boundary
        sk[T - 1] = comp ? nsl : 0xFFFFFFF0u;
        uint w[16];
        stream_block<T>(w, rw, g.rwn, cb * 64, sk);
        shst r = sha_blk(A, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]);
        if (comp) {
            uint zi = zs + k, ic = il + 1 + k;
            uint4 *zo = (uint4 *)(zbuf + zi * 8);
            zo[0] = make_uint4(r.a, r.b, r.c, r.d); zo[1] = make_uint4(r.e, r.f, r.g, r.h);
            uint4 id = make_uint4(px, py, 0u, cb + 1);   // .w: the subset's next stream block
            if (T - 1 < 4) id.x |= ic << (8 * ((T - 1) & 3));
            else if (T - 1 < 8) id.y |= ic << (8 * ((T - 5) & 3));
            else id.z = ic;
            zinfo[zi] = id;
            k++;
            if (k == c) need = true;
            else nsl = soff[il + 1 + k] - g.slen * (T - 1);
        } else { A = r; cb++; }
    }
}

template <int T>
KERNEL ztail(RoundGeo g, uint *zbuf, const uint4 *zinfo, uint *ctr, const uint *rw) {
    uint nz = *(volatile uint *)&ctr[2];
    uint zi = atom_add(&ctr[3], 1u);
    if (zi >= nz) return;
    const uint *rT = rw + T * g.rwn;
    uint4 *zo = (uint4 *)(zbuf + zi * 8);
    uint4 s0 = zo[0], s1 = zo[1];
    shst S; S.a = s0.x; S.b = s0.y; S.c = s0.z; S.d = s0.w; S.e = s1.x; S.f = s1.y; S.g = s1.z; S.h = s1.w;
    uint b = zinfo[zi].w;
    for (;;) {
        bool fin = b >= g.nblk;
        const uint *src = rT + qg_min(b, g.nblk - 1) * 16;
        uint w[16];
#pragma unroll
        for (int i = 0; i < 16; i++) w[i] = src[i];
        if (fin) {
            w[0] = S.a; w[1] = S.b; w[2] = S.c; w[3] = S.d; w[4] = S.e; w[5] = S.f; w[6] = S.g; w[7] = S.h;
            w[8] = 0x80000000u; w[9] = 0; w[10] = 0; w[11] = 0; w[12] = 0; w[13] = 0; w[14] = 0; w[15] = 256u;
        }
        shst in = fin ? SHA_IV : S;
        shst r = sha_blk(in, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]);
        if (!fin) { S = r; b++; continue; }
        zo[0] = make_uint4(r.a, r.b, r.c, r.d); zo[1] = make_uint4(r.e, r.f, r.g, r.h);
        zi = atom_add(&ctr[3], 1u);
        if (zi >= nz) break;
        zo = (uint4 *)(zbuf + zi * 8);
        s0 = zo[0]; s1 = zo[1];
        S.a = s0.x; S.b = s0.y; S.c = s0.z; S.d = s0.w; S.e = s1.x; S.f = s1.y; S.g = s1.z; S.h = s1.w;
        b = zinfo[zi].w;
    }
}

// count[0] hits, ctr[0..3] (see zpre); pin: ctr[2] = nz of the batch
KERNEL set_ctr(uint *count, uint *ctr, uint nz) {
    if (GID) return;
    count[0] = 0; ctr[0] = 0; ctr[1] = 0; ctr[2] = nz; ctr[3] = 0;
}

// ------------------------------------------------------------------------------ EC
QG_FI void store_pt(uint4 *pts, uint i, fe x, fe y) {
    x = fe_norm(x); y = fe_norm(y);
    pts[i * 4 + 0] = make_uint4(x.v7, x.v6, x.v5, x.v4);
    pts[i * 4 + 1] = make_uint4(x.v3, x.v2, x.v1, x.v0);
    pts[i * 4 + 2] = make_uint4(y.v7, y.v6, y.v5, y.v4);
    pts[i * 4 + 3] = make_uint4(y.v3, y.v2, y.v1, y.v0);
}

QG_FI gej comb(const uint *zw, const ge *table) {
    fe z; z.v0 = zw[7]; z.v1 = zw[6]; z.v2 = zw[5]; z.v3 = zw[4]; z.v4 = zw[3]; z.v5 = zw[2]; z.v6 = zw[1]; z.v7 = zw[0];
    gej w; bool inf = true;
    w.x = fe_zero(); w.y = fe_zero(); w.z = fe_zero();
    for (uint win = 0; win < 16; win++) {
        uint dg = z.v0 & 0xFFFFu;
        z.v0 = (z.v0 >> 16) | (z.v1 << 16); z.v1 = (z.v1 >> 16) | (z.v2 << 16); z.v2 = (z.v2 >> 16) | (z.v3 << 16);
        z.v3 = (z.v3 >> 16) | (z.v4 << 16); z.v4 = (z.v4 >> 16) | (z.v5 << 16); z.v5 = (z.v5 >> 16) | (z.v6 << 16);
        z.v6 = (z.v6 >> 16) | (z.v7 << 16); z.v7 >>= 16;
        if (dg) {
            ge t = table[win * 65536 + dg];
            if (inf) { w.x = t.x; w.y = t.y; w.z = fe_one(); inf = false; }
            else w = gej_add_ge(w, t);
        }
    }
    return w;
}

// One thread = ZB z-blocks, two Montgomery batches: (1) the ZB Jacobian Z's -> affine W_b (one
// inversion), (2) the menu denominators D = x_C - x_W over all ZB * NPAIR recid pairs (a second
// inversion). An affine W costs the extra inversion per thread (~57 muls / ZB) but saves the
// x_C * Z^2 product and the 1/D * Z^2 rescale per pair (2 muls x NPAIR per z-block).
// Scratch strided by thread (coalesced): [sq: NE menu prefix products][sw: x_W, y_W per z-block,
// then the menu inverse][sj: X, Y, Z, Z prefix per z-block (ec_comb only)]. The menu batch runs
// in descending b (the order the Z back pass produces affine W's); ec_menu walks it back ascending.
template <int K, int NP> struct EL {
    static constexpr uint NPAIR = K * NP / 2, NE = ZB * NPAIR;
    static constexpr uint SW = NE, SJ = NE + 2 * ZB + 1, SCR_FE = SJ + 4 * ZB;
};

template <int K, int NP>
#if QG_LB_COMB && defined(__CUDACC__) && !defined(QG_EMU)
__launch_bounds__(QG_TPB, QG_LB_COMB)
#endif
KERNEL ec_comb(const uint *zbuf, const ge *table, fe *scratch, const uint *nzp, uint cap) {
    typedef EL<K, NP> L;
    const uint NPAIR = L::NPAIR;
    uint nz = nzp[0], gid = GID, nth = (cap + ZB - 1) / ZB;     // scratch is strided by the launch size
    if (gid >= (nz + ZB - 1) / ZB) return;
    fe *sq = scratch, *sw = scratch + (size_t)L::SW * nth, *sj = scratch + (size_t)L::SJ * nth;
    fe q = fe_one();
    for (uint b = 0; b < ZB; b++) {
        uint zi = qg_min(gid * ZB + b, nz - 1);
        gej W = comb(zbuf + zi * 8, table);
        q = b ? fe_mul(q, W.z) : W.z;
        sj[(4 * b) * nth + gid] = W.x; sj[(4 * b + 1) * nth + gid] = W.y;
        sj[(4 * b + 2) * nth + gid] = W.z; sj[(4 * b + 3) * nth + gid] = q;
    }
    fe inv = fe_inv_sg(q);                           // 1 / prod Z
    fe q2 = fe_one();
    uint s = 0;
    for (int b = ZB - 1; b >= 0; b--) {              // Z back pass, fused with the menu's forward pass
        fe zi = b ? fe_mul(inv, sj[(4 * b - 1) * nth + gid]) : inv;
        if (b) inv = fe_mul(inv, sj[(4 * b + 2) * nth + gid]);
        fe zi2 = fe_sqr(zi);
        fe xW = fe_mul(sj[(4 * b) * nth + gid], zi2);
        fe yW = fe_mul(sj[(4 * b + 1) * nth + gid], fe_mul(zi2, zi));
        sw[(2 * b) * nth + gid] = xW; sw[(2 * b + 1) * nth + gid] = yW;
        for (uint p = 0; p < NPAIR; p++, s++) {
            fe D = fe_sub(c_cpts[2 * p].x, xW);
            q2 = s ? fe_mul(q2, D) : D;
            sq[s * nth + gid] = q2;
        }
    }
#if QG_STAGE == 2
    if (q2.v0 == 0x9E3779B9u) sw[0] = q2;           // keep the work alive
    return;
#endif
    sw[(2 * ZB) * nth + gid] = fe_inv_sg(q2);
}

template <int K, int NP, int NENC, int H>
#if QG_LB_MENU && defined(__CUDACC__) && !defined(QG_EMU)
__launch_bounds__(QG_TPB, QG_LB_MENU)
#endif
KERNEL ec_menu(fe *scratch, uint4 *pts, const uint *nzp, uint cap, const uint4 *zinfo, uint *count, Hit *hits) {
    typedef EL<K, NP> L;
    const uint NPAIR = L::NPAIR, NE = L::NE, PPZ = K * NP;
    uint nz = nzp[0], gid = GID, nth = (cap + ZB - 1) / ZB;
    if (gid >= (nz + ZB - 1) / ZB) return;
    fe *sq = scratch, *sw = scratch + (size_t)L::SW * nth;
    fe inv = sw[(2 * ZB) * nth + gid];
#if QG_STAGE == 3
    if (inv.v0 == 0x9E3779B9u) sw[1] = inv;
    return;
#endif
#if QG_STAGE == 4
    uint acc4 = 0;
#endif
    fe xW = fe_zero(), yW = fe_zero();
    for (int s = NE - 1; s >= 0; s--) {               // b ascending (the forward pass ran b descending)
        uint b = ZB - 1 - (uint)s / NPAIR, p = (uint)s % NPAIR;
        if (p == NPAIR - 1) { xW = sw[(2 * b) * nth + gid]; yW = sw[(2 * b + 1) * nth + gid]; }
        ge c0 = c_cpts[2 * p], c1 = c_cpts[2 * p + 1];
        fe D = fe_sub(c0.x, xW);
        fe il = s > 0 ? fe_mul(inv, sq[(s - 1) * nth + gid]) : inv;     // 1/(x_C - x_W)
        if (s > 0) inv = fe_mul(inv, D);
        fe l0 = fe_mul(fe_sub(c0.y, yW), il);
        fe x0 = fe_sub(fe_sub(fe_sqr(l0), xW), c0.x);
        fe y0 = fe_sub(fe_mul(l0, fe_sub(xW, x0)), yW);
        fe l1 = fe_mul(fe_sub(c1.y, yW), il);
        fe x1 = fe_sub(fe_sub(fe_sqr(l1), xW), c1.x);
        fe y1 = fe_sub(fe_mul(l1, fe_sub(xW, x1)), yW);
#if QG_STAGE == 4
        acc4 ^= x0.v0 ^ y0.v1 ^ x1.v2 ^ y1.v3; continue;
#endif
        uint zi = gid * ZB + b;
        if (zi >= nz) continue;
#if QG_FUSE
        hash_point<NP, NENC, H>(x0, y0, 2 * p, zi, zinfo, count, hits);
        hash_point<NP, NENC, H>(x1, y1, 2 * p + 1, zi, zinfo, count, hits);
#else
        store_pt(pts, zi * PPZ + 2 * p, x0, y0);
        store_pt(pts, zi * PPZ + 2 * p + 1, x1, y1);
#endif
    }
#if QG_STAGE == 4
    if (acc4 == 0x9E3779B9u) sw[2].v0 = acc4;
#endif
}

// one thread per (point, encoding); each 1/NE of the grid is one encoding (warp-uniform)
template <int K, int NP, int NE, int H>
KERNEL hash_pts(const uint4 *pts, const uint4 *zinfo, uint *count, Hit *hits, const uint *nzp) {
    const uint PPZ = K * NP;
    uint tid = GID, npts = nzp[0] * PPZ;
    uint e = tid / npts, gid = tid - e * npts;
    if (e >= (uint)NE) return;
    uint zi = gid / PPZ;
    uint4 X0 = pts[gid * 4], X1 = pts[gid * 4 + 1];
    uint x0 = X0.x, x1 = X0.y, x2 = X0.z, x3 = X0.w, x4 = X1.x, x5 = X1.y, x6 = X1.z, x7 = X1.w;
    uint jr = gid - zi * PPZ;
    uint c = (jr / NP) | ((jr % NP) << 8) | (e << 16);
    shst s;
    if (e == 0) {
        uint par = pts[gid * 4 + 3].w & 1u;
        s = sha_blk(SHA_IV, 0x02000000u | (par << 24) | (x0 >> 8), (x0 << 24) | (x1 >> 8), (x1 << 24) | (x2 >> 8),
                    (x2 << 24) | (x3 >> 8), (x3 << 24) | (x4 >> 8), (x4 << 24) | (x5 >> 8), (x5 << 24) | (x6 >> 8),
                    (x6 << 24) | (x7 >> 8), (x7 << 24) | 0x00800000u, 0u, 0u, 0u, 0u, 0u, 0u, 264u);
    } else {
#if QG_STAGE == 6
        return;
#endif
        uint4 Y0 = pts[gid * 4 + 2], Y1 = pts[gid * 4 + 3];
        uint y0 = Y0.x, y1 = Y0.y, y2 = Y0.z, y3 = Y0.w, y4 = Y1.x, y5 = Y1.y, y6 = Y1.z, y7 = Y1.w;
        uint pfx = e == 1 ? 0x04000000u : (0x06000000u | ((y7 & 1u) << 24));
        s = sha_blk(SHA_IV, pfx | (x0 >> 8), (x0 << 24) | (x1 >> 8), (x1 << 24) | (x2 >> 8),
                    (x2 << 24) | (x3 >> 8), (x3 << 24) | (x4 >> 8), (x4 << 24) | (x5 >> 8), (x5 << 24) | (x6 >> 8),
                    (x6 << 24) | (x7 >> 8), (x7 << 24) | (y0 >> 8), (y0 << 24) | (y1 >> 8), (y1 << 24) | (y2 >> 8),
                    (y2 << 24) | (y3 >> 8), (y3 << 24) | (y4 >> 8), (y4 << 24) | (y5 >> 8), (y5 << 24) | (y6 >> 8),
                    (y6 << 24) | (y7 >> 8));
        s = sha_blk(s, (y7 << 24) | 0x00800000u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u, 520u);
    }
#if QG_STAGE == 6 || QG_STAGE == 7
    if (s.a == 0x9E3779B9u) atom_add(count, 1u);
    return;
#endif
    uint4 id = zinfo[zi];
    if (gate(s.a)) emit(count, hits, id, c | (1u << 24));
    for (uint lvl = 2; lvl <= (uint)H; lvl++) {
        s = sha_of_digest(s);
        if (gate(s.a)) emit(count, hits, id, c | (lvl << 24));
    }
}

// ------------------------------------------------------------------------------ device API
#if defined(__CUDACC__) && !defined(QG_EMU)
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { fprintf(stderr, "CUDA %s: %s\n", #x, cudaGetErrorString(e_)); exit(5); } } while (0)
typedef cudaStream_t qstream;
static void *dalloc(size_t n) { void *p = nullptr; CK(cudaMalloc(&p, n)); return p; }
static void h2d(void *d, const void *h, size_t n) { CK(cudaMemcpy(d, h, n, cudaMemcpyHostToDevice)); }
static void d2h(void *h, const void *d, size_t n) { CK(cudaMemcpy(h, d, n, cudaMemcpyDeviceToHost)); }
static void *halloc(size_t n) { void *p = nullptr; CK(cudaMallocHost(&p, n)); return p; }
static void d2h_async(void *h, const void *d, size_t n, qstream st) { CK(cudaMemcpyAsync(h, d, n, cudaMemcpyDeviceToHost, st)); }
static void dzero_async(void *d, size_t n, qstream st) { CK(cudaMemsetAsync(d, 0, n, st)); }
#define LAUNCH(k, n, tpb, st, ...) do { size_t n_ = (n); if (n_) { k<<<(unsigned)((n_ + (tpb) - 1) / (tpb)), (tpb), 0, (st)>>>(__VA_ARGS__); CK(cudaGetLastError()); } } while (0)
#define TO_SYMBOL(sym, src, n) CK(cudaMemcpyToSymbol(sym, src, n))
#else
typedef int qstream;
static void *dalloc(size_t n) { void *p = calloc(1, n); if (!p) { fprintf(stderr, "out of memory\n"); exit(5); } return p; }
static void h2d(void *d, const void *h, size_t n) { memcpy(d, h, n); }
static void d2h(void *h, const void *d, size_t n) { memcpy(h, d, n); }
static void *halloc(size_t n) { return dalloc(n); }
static void d2h_async(void *h, const void *d, size_t n, qstream) { memcpy(h, d, n); }
static void dzero_async(void *d, size_t n, qstream) { memset(d, 0, n); }
template <typename F> static void emu_for(size_t n, F f) {
    unsigned nt = std::max(1u, std::thread::hardware_concurrency());
    std::atomic<size_t> next(0);
    std::vector<std::thread> th;
    for (unsigned t = 0; t < nt; t++) th.emplace_back([&] {
        for (size_t i; (i = next.fetch_add(64)) < n;)
            for (size_t k = i; k < std::min(n, i + 64); k++) { qg_gid = (uint)k; f(); }
    });
    for (auto &t : th) t.join();
}
#define LAUNCH(k, n, tpb, st, ...) do { size_t n_ = ((size_t)(n) + (tpb) - 1) / (tpb) * (tpb); emu_for(n_, [&] { k(__VA_ARGS__); }); } while (0)
#define TO_SYMBOL(sym, src, n) memcpy(&(sym), src, n)
#endif

// ------------------------------------------------------------------------------ host SHA-256
static const uint32_t K256[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static const uint32_t IV[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
                               0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
static inline uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
static void compress(uint32_t *st, const uint8_t *p) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++) w[i] = (uint32_t)p[4*i] << 24 | (uint32_t)p[4*i+1] << 16 | (uint32_t)p[4*i+2] << 8 | p[4*i+3];
    for (int i = 16; i < 64; i++)
        w[i] = w[i-16] + (rotr(w[i-15],7) ^ rotr(w[i-15],18) ^ (w[i-15] >> 3)) + w[i-7] + (rotr(w[i-2],17) ^ rotr(w[i-2],19) ^ (w[i-2] >> 10));
    uint32_t a=st[0],b=st[1],c=st[2],d=st[3],e=st[4],f=st[5],g=st[6],h=st[7];
    for (int i = 0; i < 64; i++) {
        uint32_t t1 = h + (rotr(e,6)^rotr(e,11)^rotr(e,25)) + ((e&f)^(~e&g)) + K256[i] + w[i];
        uint32_t t2 = (rotr(a,2)^rotr(a,13)^rotr(a,22)) + ((a&b)^(a&c)^(b&c));
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    st[0]+=a; st[1]+=b; st[2]+=c; st[3]+=d; st[4]+=e; st[5]+=f; st[6]+=g; st[7]+=h;
}

// ------------------------------------------------------------------------------ host secp256k1
// The 16 comb window bases 2^(16w) * B, affine (setup only, ~1 ms).
typedef unsigned __int128 u128;
struct U256 { uint64_t w[4]; };
static const U256 PP = {{0xFFFFFFFEFFFFFC2Full, ~0ull, ~0ull, ~0ull}};
static bool geq(const U256 &a, const U256 &b) {
    for (int i = 3; i >= 0; i--) { if (a.w[i] != b.w[i]) return a.w[i] > b.w[i]; }
    return true;
}
static U256 addm(U256 a, const U256 &b) {
    u128 c = 0; for (int i = 0; i < 4; i++) { c += (u128)a.w[i] + b.w[i]; a.w[i] = (uint64_t)c; c >>= 64; }
    if (c || geq(a, PP)) { u128 d = 0; for (int i = 0; i < 4; i++) { d = (u128)a.w[i] - PP.w[i] - (uint64_t)d; a.w[i] = (uint64_t)d; d = (d >> 64) & 1; } }
    return a;
}
static U256 subm(U256 a, const U256 &b) {
    u128 d = 0; for (int i = 0; i < 4; i++) { d = (u128)a.w[i] - b.w[i] - (uint64_t)d; a.w[i] = (uint64_t)d; d = (d >> 64) & 1; }
    if (d) { u128 c = 0; for (int i = 0; i < 4; i++) { c += (u128)a.w[i] + PP.w[i]; a.w[i] = (uint64_t)c; c >>= 64; } }
    return a;
}
static U256 mulm(const U256 &a, const U256 &b) {
    uint64_t t[8] = {0};
    for (int i = 0; i < 4; i++) {
        u128 c = 0;
        for (int j = 0; j < 4; j++) { c += (u128)a.w[i] * b.w[j] + t[i + j]; t[i + j] = (uint64_t)c; c >>= 64; }
        t[i + 4] = (uint64_t)c;
    }
    for (int round = 0; round < 2; round++) {
        u128 c = 0; uint64_t hi[4] = {t[4], t[5], t[6], t[7]};
        for (int i = 0; i < 4; i++) { c += (u128)hi[i] * 0x1000003D1ull + t[i]; t[i] = (uint64_t)c; c >>= 64; }
        t[4] = (uint64_t)c; t[5] = t[6] = t[7] = 0;
    }
    U256 r = {{t[0], t[1], t[2], t[3]}};
    if (t[4]) { U256 k = {{0x1000003D1ull * t[4], 0, 0, 0}}; r = addm(r, k); }
    while (geq(r, PP)) r = subm(r, PP);
    return r;
}
static U256 invm(const U256 &a) {
    U256 e = PP; e.w[0] -= 2; U256 r = {{1, 0, 0, 0}}, b = a;
    for (int i = 0; i < 256; i++) { if ((e.w[i / 64] >> (i % 64)) & 1) r = mulm(r, b); b = mulm(b, b); }
    return r;
}
static void window_bases(const uint32_t *B32, uint32_t *out) {   // 16 x (x, y), 8 LE 32-bit limbs each
    U256 x, y;
    for (int i = 0; i < 4; i++) { x.w[i] = (uint64_t)B32[2 * i] | (uint64_t)B32[2 * i + 1] << 32; y.w[i] = (uint64_t)B32[8 + 2 * i] | (uint64_t)B32[8 + 2 * i + 1] << 32; }
    for (int w = 0; w < 16; w++) {
        if (w) for (int k = 0; k < 16; k++) {
            U256 x2 = mulm(x, x), num = addm(addm(x2, x2), x2), den = invm(addm(y, y));
            U256 l = mulm(num, den), nx = subm(subm(mulm(l, l), x), x);
            y = subm(mulm(l, subm(x, nx)), y); x = nx;
        }
        for (int i = 0; i < 4; i++) {
            out[w * 16 + 2 * i] = (uint32_t)x.w[i]; out[w * 16 + 2 * i + 1] = (uint32_t)(x.w[i] >> 32);
            out[w * 16 + 8 + 2 * i] = (uint32_t)y.w[i]; out[w * 16 + 8 + 2 * i + 1] = (uint32_t)(y.w[i] >> 32);
        }
    }
}

// ------------------------------------------------------------------------------ problem (P.txt)
struct Problem {
    std::string track, kind;
    int gate_bits = 0, K = 0, npts = 0, nenc = 0, H = 0, t = 0, n_slots = 0, slot_len = 0;
    int seq_off = 0, lt_off = 0;
    uint32_t tag = 0;
    std::vector<uint32_t> slot_offs, B = std::vector<uint32_t>(16), C;
    std::vector<uint8_t> pre;
};

static void fe_from_hex(const std::string &s, uint32_t *limbs) {   // 64 hex chars BE -> 8 LE limbs
    for (int i = 0; i < 8; i++) limbs[7 - i] = (uint32_t)strtoul(s.substr(8 * i, 8).c_str(), nullptr, 16);
}

static Problem load(const std::string &json_path) {
    std::string p = json_path;
    size_t dot = p.rfind('.');
    p = (dot == std::string::npos ? p : p.substr(0, dot)) + ".txt";
    std::ifstream f(p);
    if (!f) { fprintf(stderr, "cannot read %s\n", p.c_str()); exit(2); }
    Problem P;
    std::string line;
    std::vector<std::vector<std::string>> cs;
    while (std::getline(f, line)) {
        std::istringstream ss(line);
        std::string k; ss >> k;
        if (k == "track") ss >> P.track;
        else if (k == "kind") ss >> P.kind;
        else if (k == "gate_bits") ss >> P.gate_bits;
        else if (k == "gate_tag") { long long v; ss >> v; P.tag = (uint32_t)v; }
        else if (k == "K") ss >> P.K;
        else if (k == "npts") ss >> P.npts;
        else if (k == "nenc") ss >> P.nenc;
        else if (k == "H") ss >> P.H;
        else if (k == "t") ss >> P.t;
        else if (k == "n_slots") ss >> P.n_slots;
        else if (k == "slot_len") ss >> P.slot_len;
        else if (k == "seq_off") ss >> P.seq_off;
        else if (k == "lt_off") ss >> P.lt_off;
        else if (k == "slot") { int i; uint32_t o; ss >> i >> o; if ((int)P.slot_offs.size() != i) exit(2); P.slot_offs.push_back(o); }
        else if (k == "B") { std::string x, y; ss >> x >> y; fe_from_hex(x, &P.B[0]); fe_from_hex(y, &P.B[8]); }
        else if (k == "C") { std::string j, r, x, y; ss >> j >> r >> x >> y; cs.push_back({j, r, x, y}); }
        else if (k == "preimage") {
            std::string h; ss >> h;
            P.pre.resize(h.size() / 2);
            for (size_t i = 0; i < P.pre.size(); i++) P.pre[i] = (uint8_t)strtoul(h.substr(2 * i, 2).c_str(), nullptr, 16);
        }
    }
    P.C.assign((size_t)P.K * P.npts * 16, 0);
    for (auto &c : cs) {
        int j = atoi(c[0].c_str()), r = atoi(c[1].c_str());
        fe_from_hex(c[2], &P.C[(j * P.npts + r) * 16]);
        fe_from_hex(c[3], &P.C[(j * P.npts + r) * 16 + 8]);
    }
    return P;
}

// ------------------------------------------------------------------------------ the grind loop
struct Slot {
    uint *zbuf, *count, *ctr;
    uint4 *zinfo, *pts;
    fe *scratch;
    Hit *hits, *hhits;
    uint *hcount;
    qstream st;
#if defined(__CUDACC__) && !defined(QG_EMU)
    cudaEvent_t e0, e1;
#endif
    uint nz = 0;
    double t0 = 0;
};

template <int K, int NP, int NE, int H, int T>
static int grind(const Problem &P, const std::string &hitsPath, double seconds,
                 std::chrono::steady_clock::time_point t0) {
    auto elapsed = [&] { return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); };
    constexpr bool ROUND = T > 0;
    const uint PPZ = K * NP, NPAIR = PPZ / 2;
    for (uint p = 0; p < NPAIR; p++)                // a recid pair must share x
        if (memcmp(&P.C[(2 * p) * 16], &P.C[(2 * p + 1) * 16], 32)) { fprintf(stderr, "C[j][2h].x != C[j][2h+1].x\n"); return 2; }
    const bool timing = getenv("QG_TIMING") != nullptr;   // setup phase times (diagnostic only)
    auto mark = [&](const char *what) { if (timing) printf("@timing %s %.3f\n", what, elapsed()); };
    mark("start");
    uint32_t gatev[2] = {(uint32_t)P.gate_bits, P.tag};
    TO_SYMBOL(c_gate, gatev, sizeof gatev);
    TO_SYMBOL(c_cpts, P.C.data(), P.C.size() * 4);
    const std::vector<uint8_t> &pre = P.pre;

    mark("context+consts");
    // ---- host precomputation
    PinParams pp = {};
    std::vector<uint32_t> rwords, mids;
    RoundGeo geo = {};
    uint rwn = 0, nblk = 0;
    qg_u64 seed = 0;
    if (!ROUND) {
        size_t start = (size_t)(P.seq_off / 64) * 64;
        uint32_t st[8]; memcpy(st, IV, 32);
        for (size_t o = 0; o < start; o += 64) compress(st, &pre[o]);
        memcpy(pp.mid, st, 32);
        uint8_t tail[128] = {0};
        size_t tl = pre.size() - start;
        if (tl + 9 > 128 || P.lt_off < (int)start) { fprintf(stderr, "tail too long\n"); return 4; }
        pp.nblk = (uint)((tl + 9 + 63) / 64);
        memcpy(tail, &pre[start], tl);
        tail[tl] = 0x80;
        uint64_t bitlen = (uint64_t)pre.size() * 8;
        for (int i = 0; i < 8; i++) tail[pp.nblk * 64 - 1 - i] = (uint8_t)(bitlen >> (8 * i));
        for (int i = 0; i < 32; i++) pp.tail[i] = (uint32_t)tail[4*i] << 24 | (uint32_t)tail[4*i+1] << 16 | (uint32_t)tail[4*i+2] << 8 | tail[4*i+3];
        pp.seq_pos = (uint)(P.seq_off - start); pp.lt_pos = (uint)(P.lt_off - start);
    } else {
        int slen = P.slot_len;
        for (size_t i = 1; i < P.slot_offs.size(); i++)
            if (P.slot_offs[i] < P.slot_offs[i - 1] + (uint32_t)slen + 12) { fprintf(stderr, "slots too close\n"); return 4; }
        size_t L = pre.size(), Lm = L - (size_t)T * slen;
        nblk = (uint)((Lm + 9 + 63) / 64);
        std::vector<uint8_t> E(pre);
        size_t lenAt = (size_t)nblk * 64 - 8 + (size_t)T * slen;
        E.resize(lenAt + 16, 0);
        E[L] = 0x80;
        uint64_t bitlen = (uint64_t)Lm * 8;
        for (int i = 0; i < 8; i++) E[lenAt + 7 - i] = (uint8_t)(bitlen >> (8 * i));
        size_t nw = (size_t)nblk * 16;
        auto be = [&](size_t o) { return o + 3 < E.size() ? (uint32_t)E[o] << 24 | (uint32_t)E[o+1] << 16 | (uint32_t)E[o+2] << 8 | E[o+3] : 0u; };
        rwords.assign(nw * (T + 2), 0);             // + 1 spare region: the branch-free merge reads k + 1
        for (int r = 0; r <= T; r++) for (size_t m = 0; m < nw; m++) rwords[r * nw + m] = be(4 * m + (size_t)slen * r);
        rwn = (uint)nw;
        geo.nslots = (uint)P.n_slots; geo.slen = (uint)slen; geo.nblk = nblk; geo.rwn = rwn;
        size_t nb = L / 64 + 1;
        mids.resize(nb * 8);
        uint32_t st[8]; memcpy(st, IV, 32);
        for (size_t b = 0; b < nb; b++) {
            memcpy(&mids[b * 8], st, 32);
            if ((b + 1) * 64 <= L) compress(st, &pre[b * 64]);
        }
        FILE *ur = fopen("/dev/urandom", "rb");
        if (!ur || fread(&seed, sizeof seed, 1, ur) != 1) { fprintf(stderr, "no /dev/urandom\n"); return 4; }
        fclose(ur);
    }

    mark("host-pre");
    // ---- device buffers (QG_NSLOT slots in flight)
    uint NZ_MAX = 1u << 21;                        // z-blocks per batch (fused pipeline: no point buffer, so large batches are cheap)
    if (const char *e = getenv("QG_NZ_MAX")) NZ_MAX = (uint)atoi(e);
#if defined(QG_EMU)
    NZ_MAX = 1u << 13;
#endif
    const uint NZ_CAP = NZ_MAX + ZSLACK;
    Slot slots[QG_NSLOT];
    size_t scr = (size_t)(NZ_CAP / ZB + 1) * EL<K, NP>::SCR_FE * sizeof(fe);
    scr = std::max(scr, (size_t)16 * 65536 * sizeof(fe));
    for (Slot &s : slots) {
        s.zbuf = (uint *)dalloc((size_t)NZ_CAP * 32);
        s.zinfo = (uint4 *)dalloc((size_t)NZ_CAP * 16);
        s.scratch = (fe *)dalloc(scr);
        s.pts = (uint4 *)dalloc(QG_FUSE ? 64 : (size_t)NZ_CAP * PPZ * 64);   // fused: no point buffer
        s.count = (uint *)dalloc(32);
        s.ctr = s.count + 4;
        s.hits = (Hit *)dalloc((size_t)HIT_CAP * sizeof(Hit));
        s.hhits = (Hit *)malloc((size_t)HIT_CAP * sizeof(Hit));      // pageable: 32 MB pinned cost ~40 ms of setup + teardown
        s.hcount = (uint *)halloc(32);
#if defined(__CUDACC__) && !defined(QG_EMU)
        CK(cudaStreamCreateWithFlags(&s.st, cudaStreamNonBlocking));    // no implicit sync with the other slot
        CK(cudaEventCreate(&s.e0)); CK(cudaEventCreate(&s.e1));
#else
        s.st = 0;
#endif
    }
    uint *rwd = nullptr, *midd = nullptr, *soffd = nullptr;
    if (ROUND) {
        rwd = (uint *)dalloc(rwords.size() * 4); h2d(rwd, rwords.data(), rwords.size() * 4);
        midd = (uint *)dalloc(mids.size() * 4); h2d(midd, mids.data(), mids.size() * 4);
        soffd = (uint *)dalloc(P.slot_offs.size() * 4); h2d(soffd, P.slot_offs.data(), P.slot_offs.size() * 4);
    }

    mark("buffers");
    // ---- comb table
    std::vector<uint32_t> bases(16 * 16);
    window_bases(P.B.data(), bases.data());
    ge *table = (ge *)dalloc((size_t)16 * 65536 * sizeof(ge));
    ge *based = (ge *)dalloc(bases.size() * 4);
    h2d(based, bases.data(), bases.size() * 4);
    LAUNCH(build_table, 16 * (65536 / TB_CHUNK), 64, slots[0].st, table, based, slots[0].scratch, slots[1].scratch);
#if defined(__CUDACC__) && !defined(QG_EMU)
    CK(cudaDeviceSynchronize());
    mark("table");
    cudaFuncAttributes fa;
    CK(cudaFuncGetAttributes(&fa, ec_menu<K, NP, NE, H>));
    int dev = 0; cudaDeviceProp prop; CK(cudaGetDevice(&dev)); CK(cudaGetDeviceProperties(&prop, dev));
    printf("@setup {\"t_s\": %.3f, \"kernel\": \"ec_menu\", \"device\": \"%s\", \"max_threads_per_tg\": %d, "
           "\"regs\": %d, \"local_bytes\": %zu, \"simd_width\": 32, \"tg_used\": 128}\n",
           elapsed(), prop.name, fa.maxThreadsPerBlock, fa.numRegs, fa.localSizeBytes);
#else
    printf("@setup {\"t_s\": %.3f, \"kernel\": \"ec_menu\", \"device\": \"cpu-emulation\", \"max_threads_per_tg\": 1, \"simd_width\": 1, \"tg_used\": 1}\n", elapsed());
#endif
    fflush(stdout);

    // ---- batches
    FILE *out = fopen(hitsPath.c_str(), "w");
    if (!out) { fprintf(stderr, "cannot write %s\n", hitsPath.c_str()); return 2; }
    // pin z-blocks = (nSequence, nLockTime), restricted to values a real spend can use: nSequence has
    // the BIP68 disable bit set (0x80000000..0xFFFFFFFD: no relative lock, not final), and since the
    // input is then not final, nLockTime must be in the past: timestamps [5e8, 1.7e9) (Nov 2023). Both
    // start at random points, so restarted or parallel runs (interruptible instances, many GPUs)
    // grind disjoint candidates instead of repeating seq 0, lt 0.
    const uint64_t LT_LO = 500000000ull, LT_HI = 1700000000ull;
    const uint32_t SEQ_LO = 0x80000000u, SEQ_N = 0x7FFFFFFEu;
    uint64_t rnd[2] = {0, 0};
    if (!ROUND) {
        FILE *ur = fopen("/dev/urandom", "rb");
        if (!ur || fread(rnd, sizeof rnd, 1, ur) != 1) { fprintf(stderr, "no /dev/urandom\n"); return 4; }
        fclose(ur);
    }
    uint64_t lt_next = LT_LO + rnd[0] % (LT_HI - LT_LO), zblocks = 0;
    uint32_t seq = SEQ_LO + (uint32_t)(rnd[1] % SEQ_N);
    uint nz = std::min(NZ_MAX, 1u << 16);
    const double target = 0.1;                     // seconds of GPU per batch
    double last_done = elapsed(), per_z = 0, t_ref = 0;
    uint64_t z_ref = 0;
    int nbatches = 0;
    const int TPB = QG_TPB;

    auto submit = [&](Slot &s) {
        s.nz = nz;
        LAUNCH(set_ctr, 1, 32, s.st, s.count, s.ctr, ROUND ? 0u : nz);
        const uint cap = ROUND ? nz + ZSLACK : nz;          // round: the GPU decides nz <= cap
#if defined(__CUDACC__) && !defined(QG_EMU)
        CK(cudaEventRecord(s.e0, s.st));
#endif
        s.t0 = elapsed();
        if constexpr (!ROUND) {
            if (lt_next + nz > LT_HI) { lt_next = LT_LO; seq = SEQ_LO + (seq - SEQ_LO + 1) % SEQ_N; }
            pp.seq = seq; pp.lt_base = (uint32_t)lt_next;
            lt_next += nz;
            LAUNCH(zgen_pin, nz, TPB, s.st, pp, s.zbuf, s.zinfo, nz);
        } else {
            seed = seed * 6364136223846793005ull + 1442695040888963407ull;
            LAUNCH(zpre<T>, LANES, 64, s.st, seed, nz, geo, s.zbuf, s.zinfo, s.ctr, rwd, soffd, midd);
            LAUNCH(ztail<T>, LANES, 64, s.st, geo, s.zbuf, s.zinfo, s.ctr, rwd);
        }
        uint nth = (cap + ZB - 1) / ZB;
        const uint *nzp = s.ctr + 2;
        if (QG_STAGE >= 2) LAUNCH((ec_comb<K, NP>), nth, TPB, s.st, s.zbuf, table, s.scratch, nzp, cap);
        if (QG_STAGE >= 3) LAUNCH((ec_menu<K, NP, NE, H>), nth, TPB, s.st, s.scratch, s.pts, nzp, cap, s.zinfo, s.count, s.hits);
        if (QG_STAGE >= 6 && !QG_FUSE)
            LAUNCH((hash_pts<K, NP, NE, H>), (size_t)cap * PPZ * NE, TPB, s.st, s.pts, s.zinfo, s.count, s.hits, nzp);
#if defined(__CUDACC__) && !defined(QG_EMU)
        CK(cudaEventRecord(s.e1, s.st));
#endif
    };
    auto finish = [&](Slot &s) -> int {
#if defined(__CUDACC__) && !defined(QG_EMU)
        CK(cudaEventSynchronize(s.e1));
        float ms = 0; CK(cudaEventElapsedTime(&ms, s.e0, s.e1));
        double gpu = ms * 1e-3;
#else
        double gpu = elapsed() - s.t0;
#endif
        double now = elapsed();
        d2h_async(s.hcount, s.count, 32, s.st);
#if defined(__CUDACC__) && !defined(QG_EMU)
        CK(cudaStreamSynchronize(s.st));
#endif
        uint n = s.hcount[0];
        s.nz = s.hcount[4 + 2];                     // round: accepted z-blocks (>= budget)
        double wall = now - last_done;
        printf("@batch {\"z\": %u, \"gpu_ms\": %.3f, \"wall_ms\": %.3f, \"hits\": %u}\n", s.nz, gpu * 1e3, wall * 1e3, n);
        last_done = now;
        nbatches++;
        zblocks += s.nz;
        if (n > HIT_CAP) { fprintf(stderr, "warning: hit buffer overflow, %u lost\n", n - HIT_CAP); n = HIT_CAP; }
        if (QG_STAGE >= 99 && n) {
            d2h_async(s.hhits, s.hits, (size_t)n * sizeof(Hit), s.st);
#if defined(__CUDACC__) && !defined(QG_EMU)
            CK(cudaStreamSynchronize(s.st));
#endif
            for (uint i = 0; i < n; i++) {
                const Hit &h = s.hhits[i];
                uint j = h.c & 0xFF, rid = (h.c >> 8) & 0xFF, enc = (h.c >> 16) & 0xFF, lvl = h.c >> 24;
                if (!ROUND) fprintf(out, "%u %u %u %u %u %u\n", h.a, h.b, j, rid, enc, lvl);
                else {
                    uint32_t w[3] = {h.a, h.b, h.d};
                    for (int k = 0; k < T; k++) fprintf(out, k ? ",%u" : "%u", (w[k >> 2] >> (8 * (k & 3))) & 0xFF);
                    fprintf(out, " %u %u %u %u\n", j, rid, enc, lvl);
                }
            }
            fflush(out);
        }
        if (nbatches == 1) { t_ref = now; z_ref = zblocks; }
        else if (zblocks - z_ref >= 65536) {
            per_z = (now - t_ref) / (double)(zblocks - z_ref);
            nz = (uint)std::min((double)NZ_MAX, std::max(4096.0, target / per_z)) / 256 * 256;
        }
        return 0;
    };
    auto fit = [&](double busy_until) -> bool {     // the last batches shrink to end at the deadline
        double avail = seconds - 0.03 - busy_until;
        if (per_z <= 0) return avail > 0.5;
        uint n = (uint)std::max(0.0, avail / per_z) / 256 * 256;
        if (n < 4096) return false;
        nz = std::min(nz, n);
        return true;
    };
    bool live[QG_NSLOT];
    for (int i = 0; i < QG_NSLOT; i++) { submit(slots[i]); live[i] = true; }
    int cur = 0, nlive = QG_NSLOT;
    while (nlive) {
        Slot &s = slots[cur];
        if (live[cur]) {
            if (int rc = finish(s)) return rc;
            live[cur] = false; nlive--;
            double now = elapsed(), other = 0;      // the in-flight batches run until ~now + their durations
            for (int i = 0; i < QG_NSLOT; i++) if (live[i]) other += slots[i].nz * per_z;
            if (fit(now + other)) { submit(s); live[cur] = true; nlive++; }
        }
        cur = (cur + 1) % QG_NSLOT;
    }
    fclose(out);
    printf("@done {\"zblocks\": %llu, \"elapsed_s\": %.3f}\n", (unsigned long long)zblocks, elapsed());
    fflush(stdout);
    _exit(0);                                      // skip freeing GBs of device buffers
}

int main(int argc, const char **argv) {
    auto t0 = std::chrono::steady_clock::now();
    std::string probPath, hitsPath;
    double seconds = 10;
    for (int i = 1; i + 1 < argc; i += 2) {
        std::string k = argv[i];
        if (k == "--problem") probPath = argv[i + 1];
        else if (k == "--hits") hitsPath = argv[i + 1];
        else if (k == "--seconds") seconds = atof(argv[i + 1]);
    }
#if defined(__CUDACC__) && !defined(QG_EMU)
    // One hardware work queue per stream in flight (default 8): each connection costs ~25-30 ms
    // of context setup + teardown, ~3 % of a 4 s run. Must be set before the first CUDA call.
    { char v[8]; snprintf(v, sizeof v, "%d", QG_NCONN); setenv("CUDA_DEVICE_MAX_CONNECTIONS", v, 1); }
    CK(cudaSetDeviceFlags(cudaDeviceScheduleBlockingSync));   // the host must not spin a core
#endif
    Problem P = load(probPath);
    if (P.gate_bits < 1 || P.gate_bits > 32 || P.pre.empty()) { fprintf(stderr, "bad problem\n"); return 2; }
    // The PQB track shapes (pqb's gpu.problem_from_packet). A new shape needs one more instance here.
    if (P.kind == "pin" && P.K == 12 && P.npts == 2 && P.nenc == 3 && P.H == 1)
        return grind<12, 2, 3, 1, 0>(P, hitsPath, seconds, t0);
    if (P.kind == "round" && P.K == 16 && P.npts == 4 && P.nenc == 3 && P.H == 1 && P.t == 8)
        return grind<16, 4, 3, 1, 8>(P, hitsPath, seconds, t0);
    if (P.kind == "round" && P.K == 16 && P.npts == 4 && P.nenc == 1 && P.H == 1 && P.t == 9)
        return grind<16, 4, 1, 1, 9>(P, hitsPath, seconds, t0);
    fprintf(stderr, "no kernel instance for track %s (K=%d npts=%d nenc=%d H=%d t=%d)\n",
            P.track.c_str(), P.K, P.npts, P.nenc, P.H, P.t);
    return 2;
}
