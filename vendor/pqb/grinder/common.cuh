// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// Generated from the Metal grinder's field, inversion and SHA-256 code; edit with care.
// secp256k1 field arithmetic (8 x 32-bit scalar limbs, weakly normalized < 2^256) and an unrolled
// SHA-256 compression, for CUDA and for the CPU emulation build (-DQG_EMU, validation only).
#pragma once
#include <cstdint>
typedef unsigned int uint;
typedef unsigned long long qg_u64;      // not `ulong`: glibc's sys/types.h owns that name
typedef long long qg_i64;

#if defined(__CUDACC__) && !defined(QG_EMU)
#define QG_FI __device__ __forceinline__
#define QG_DEV __device__
#define QG_CONST __constant__
QG_FI uint qg_mulhi(uint a, uint b) { return __umulhi(a, b); }
QG_FI uint qg_rotr(uint x, uint n) { return __funnelshift_r(x, x, n); }
#else
#define QG_FI static inline
#define QG_DEV static
#define QG_CONST static const
QG_FI uint qg_mulhi(uint a, uint b) { return (uint)(((qg_u64)a * b) >> 32); }
QG_FI uint qg_rotr(uint x, uint n) { return (x >> n) | (x << ((32 - n) & 31)); }
#endif

// ---- from a_field.metal
// secp256k1 field arithmetic, 8 x 32-bit scalar limbs, weakly normalized (< 2^256).

struct fe { uint v0, v1, v2, v3, v4, v5, v6, v7; };
struct ge { fe x; fe y; };               // affine point
struct gej { fe x; fe y; fe z; };        // Jacobian point

// r += k * (2^32 + 977) for k in {0,1}; r is 256-bit. The carry past limb 1 (and a second wrap)
// only happens when r is within 2^33 of 2^256: a practically never taken branch.
QG_FI void fe_fold(fe &r, uint k) {
    uint t0 = r.v0 + 977u * k, c = (t0 < r.v0) ? 1u : 0u;
    uint y = k + c, t1 = r.v1 + y;
    r.v0 = t0; r.v1 = t1;
    if (t1 < y) {
        uint w = 1;
        r.v2 += w; w = (r.v2 == 0u); r.v3 += w; w &= (r.v3 == 0u); r.v4 += w; w &= (r.v4 == 0u);
        r.v5 += w; w &= (r.v5 == 0u); r.v6 += w; w &= (r.v6 == 0u); r.v7 += w; w &= (r.v7 == 0u);
        if (w) { uint u = r.v0 + 977u; r.v1 += 1u + ((u < 977u) ? 1u : 0u); r.v0 = u; }   // wrapped again: r < 2^33
    }
}

// branch-free variant for the mul/sqr reduction tail (k is almost always 0 there; a branch in the
// hot squaring loop of fe_inv cost ~15%)
QG_FI void fe_fold_nb(fe &r, uint k) {
    qg_u64 d = (qg_u64)r.v0 + 977u * k; r.v0 = (uint)d; d >>= 32;
    d += (qg_u64)r.v1 + k; r.v1 = (uint)d; d >>= 32;
    d += r.v2; r.v2 = (uint)d; d >>= 32;
    d += r.v3; r.v3 = (uint)d; d >>= 32;
    d += r.v4; r.v4 = (uint)d; d >>= 32;
    d += r.v5; r.v5 = (uint)d; d >>= 32;
    d += r.v6; r.v6 = (uint)d; d >>= 32;
    d += r.v7; r.v7 = (uint)d; d >>= 32;
    uint e = (uint)d;                             // wrapped again (r tiny): one more fold, no carry
    uint u = r.v0 + 977u * e; r.v1 += e + ((u < r.v0) ? 1u : 0u); r.v0 = u;
}

// r -= k * (2^32 + 977) for k in {0,1} (used after a borrow out of 2^256)
QG_FI void fe_unfold(fe &r, uint k) {
    uint s0 = 977u * k, b = (r.v0 < s0) ? 1u : 0u;
    r.v0 -= s0;
    uint y = k + b, b1 = (r.v1 < y) ? 1u : 0u;
    r.v1 -= y;
    if (b1) {
        uint w = 1;
        w = (r.v2 == 0u); r.v2 -= 1u; if (w) { w = (r.v3 == 0u); r.v3 -= 1u;
        if (w) { w = (r.v4 == 0u); r.v4 -= 1u; if (w) { w = (r.v5 == 0u); r.v5 -= 1u;
        if (w) { w = (r.v6 == 0u); r.v6 -= 1u; if (w) { w = (r.v7 == 0u); r.v7 -= 1u;
        if (w) { uint bb = (r.v0 < 977u) ? 1u : 0u; r.v0 -= 977u; r.v1 -= 1u + bb; } } } } } }   // borrowed past 2^256 again: r > 2^256 - 2^33
    }
}

QG_FI fe fe_mul(fe a, fe b) {
    qg_u64 acc = 0, p; uint c2 = 0;
    p = (qg_u64)a.v0 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t0 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t1 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t2 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t3 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t4 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t5 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v6 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t6 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v6 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v7 * b.v0;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t7 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v1 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v6 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v7 * b.v1;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t8 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v2 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v6 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v7 * b.v2;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t9 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v3 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v6 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v7 * b.v3;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t10 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v4 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v6 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v7 * b.v4;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t11 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v5 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v6 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v7 * b.v5;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t12 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v6 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v7 * b.v6;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t13 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v7 * b.v7;
    acc += p; c2 += (acc < p) ? 1u : 0u;
    uint t14 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    uint t15 = (uint)acc;
    qg_u64 c = 0;
    c += (qg_u64)t0 + (qg_u64)(t8 * 977u); uint r0 = (uint)c; c >>= 32;
    c += (qg_u64)t1 + (qg_u64)(t9 * 977u) + (qg_u64)qg_mulhi(t8, 977u) + (qg_u64)t8; uint r1 = (uint)c; c >>= 32;
    c += (qg_u64)t2 + (qg_u64)(t10 * 977u) + (qg_u64)qg_mulhi(t9, 977u) + (qg_u64)t9; uint r2 = (uint)c; c >>= 32;
    c += (qg_u64)t3 + (qg_u64)(t11 * 977u) + (qg_u64)qg_mulhi(t10, 977u) + (qg_u64)t10; uint r3 = (uint)c; c >>= 32;
    c += (qg_u64)t4 + (qg_u64)(t12 * 977u) + (qg_u64)qg_mulhi(t11, 977u) + (qg_u64)t11; uint r4 = (uint)c; c >>= 32;
    c += (qg_u64)t5 + (qg_u64)(t13 * 977u) + (qg_u64)qg_mulhi(t12, 977u) + (qg_u64)t12; uint r5 = (uint)c; c >>= 32;
    c += (qg_u64)t6 + (qg_u64)(t14 * 977u) + (qg_u64)qg_mulhi(t13, 977u) + (qg_u64)t13; uint r6 = (uint)c; c >>= 32;
    c += (qg_u64)t7 + (qg_u64)(t15 * 977u) + (qg_u64)qg_mulhi(t14, 977u) + (qg_u64)t14; uint r7 = (uint)c; c >>= 32;
    c += (qg_u64)qg_mulhi(t15, 977u) + (qg_u64)t15;
    fe r; qg_u64 d;
    d = (qg_u64)r0 + c * 977u; r.v0 = (uint)d; d >>= 32;
    d += (qg_u64)r1 + c; r.v1 = (uint)d; d >>= 32;
    d += r2; r.v2 = (uint)d; d >>= 32;
    d += r3; r.v3 = (uint)d; d >>= 32;
    d += r4; r.v4 = (uint)d; d >>= 32;
    d += r5; r.v5 = (uint)d; d >>= 32;
    d += r6; r.v6 = (uint)d; d >>= 32;
    d += r7; r.v7 = (uint)d; d >>= 32;
    fe_fold_nb(r, (uint)d);
    return r;
}
QG_FI fe fe_sqr(fe a) {
    qg_u64 acc = 0, p; uint c2 = 0;
    uint u0 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * a.v1; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u1 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * a.v2; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u2 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * a.v3; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * a.v2; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u3 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * a.v4; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * a.v3; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u4 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * a.v5; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * a.v4; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * a.v3; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u5 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * a.v6; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * a.v5; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * a.v4; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u6 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v0 * a.v7; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v1 * a.v6; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * a.v5; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * a.v4; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u7 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v1 * a.v7; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v2 * a.v6; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * a.v5; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u8 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v2 * a.v7; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v3 * a.v6; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * a.v5; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u9 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v3 * a.v7; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v4 * a.v6; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u10 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v4 * a.v7; acc += p; c2 += (acc < p) ? 1u : 0u;
    p = (qg_u64)a.v5 * a.v6; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u11 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v5 * a.v7; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u12 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    p = (qg_u64)a.v6 * a.v7; acc += p; c2 += (acc < p) ? 1u : 0u;
    uint u13 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    uint u14 = (uint)acc; acc = (acc >> 32) | ((qg_u64)c2 << 32); c2 = 0;
    uint u15 = (uint)acc;
    u15 = (u15 << 1) | (u14 >> 31);
    u14 = (u14 << 1) | (u13 >> 31);
    u13 = (u13 << 1) | (u12 >> 31);
    u12 = (u12 << 1) | (u11 >> 31);
    u11 = (u11 << 1) | (u10 >> 31);
    u10 = (u10 << 1) | (u9 >> 31);
    u9 = (u9 << 1) | (u8 >> 31);
    u8 = (u8 << 1) | (u7 >> 31);
    u7 = (u7 << 1) | (u6 >> 31);
    u6 = (u6 << 1) | (u5 >> 31);
    u5 = (u5 << 1) | (u4 >> 31);
    u4 = (u4 << 1) | (u3 >> 31);
    u3 = (u3 << 1) | (u2 >> 31);
    u2 = (u2 << 1) | (u1 >> 31);
    u1 = (u1 << 1) | (u0 >> 31);
    u0 <<= 1;
    qg_u64 cq = 0;
    p = (qg_u64)a.v0 * a.v0;
    cq += (qg_u64)u0 + (uint)p; uint t0 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u1 + (uint)(p >> 32); uint t1 = (uint)cq; cq >>= 32;
    p = (qg_u64)a.v1 * a.v1;
    cq += (qg_u64)u2 + (uint)p; uint t2 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u3 + (uint)(p >> 32); uint t3 = (uint)cq; cq >>= 32;
    p = (qg_u64)a.v2 * a.v2;
    cq += (qg_u64)u4 + (uint)p; uint t4 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u5 + (uint)(p >> 32); uint t5 = (uint)cq; cq >>= 32;
    p = (qg_u64)a.v3 * a.v3;
    cq += (qg_u64)u6 + (uint)p; uint t6 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u7 + (uint)(p >> 32); uint t7 = (uint)cq; cq >>= 32;
    p = (qg_u64)a.v4 * a.v4;
    cq += (qg_u64)u8 + (uint)p; uint t8 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u9 + (uint)(p >> 32); uint t9 = (uint)cq; cq >>= 32;
    p = (qg_u64)a.v5 * a.v5;
    cq += (qg_u64)u10 + (uint)p; uint t10 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u11 + (uint)(p >> 32); uint t11 = (uint)cq; cq >>= 32;
    p = (qg_u64)a.v6 * a.v6;
    cq += (qg_u64)u12 + (uint)p; uint t12 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u13 + (uint)(p >> 32); uint t13 = (uint)cq; cq >>= 32;
    p = (qg_u64)a.v7 * a.v7;
    cq += (qg_u64)u14 + (uint)p; uint t14 = (uint)cq; cq >>= 32;
    cq += (qg_u64)u15 + (uint)(p >> 32); uint t15 = (uint)cq; cq >>= 32;
    qg_u64 c = 0;
    c += (qg_u64)t0 + (qg_u64)(t8 * 977u); uint r0 = (uint)c; c >>= 32;
    c += (qg_u64)t1 + (qg_u64)(t9 * 977u) + (qg_u64)qg_mulhi(t8, 977u) + (qg_u64)t8; uint r1 = (uint)c; c >>= 32;
    c += (qg_u64)t2 + (qg_u64)(t10 * 977u) + (qg_u64)qg_mulhi(t9, 977u) + (qg_u64)t9; uint r2 = (uint)c; c >>= 32;
    c += (qg_u64)t3 + (qg_u64)(t11 * 977u) + (qg_u64)qg_mulhi(t10, 977u) + (qg_u64)t10; uint r3 = (uint)c; c >>= 32;
    c += (qg_u64)t4 + (qg_u64)(t12 * 977u) + (qg_u64)qg_mulhi(t11, 977u) + (qg_u64)t11; uint r4 = (uint)c; c >>= 32;
    c += (qg_u64)t5 + (qg_u64)(t13 * 977u) + (qg_u64)qg_mulhi(t12, 977u) + (qg_u64)t12; uint r5 = (uint)c; c >>= 32;
    c += (qg_u64)t6 + (qg_u64)(t14 * 977u) + (qg_u64)qg_mulhi(t13, 977u) + (qg_u64)t13; uint r6 = (uint)c; c >>= 32;
    c += (qg_u64)t7 + (qg_u64)(t15 * 977u) + (qg_u64)qg_mulhi(t14, 977u) + (qg_u64)t14; uint r7 = (uint)c; c >>= 32;
    c += (qg_u64)qg_mulhi(t15, 977u) + (qg_u64)t15;
    fe r; qg_u64 d;
    d = (qg_u64)r0 + c * 977u; r.v0 = (uint)d; d >>= 32;
    d += (qg_u64)r1 + c; r.v1 = (uint)d; d >>= 32;
    d += r2; r.v2 = (uint)d; d >>= 32;
    d += r3; r.v3 = (uint)d; d >>= 32;
    d += r4; r.v4 = (uint)d; d >>= 32;
    d += r5; r.v5 = (uint)d; d >>= 32;
    d += r6; r.v6 = (uint)d; d >>= 32;
    d += r7; r.v7 = (uint)d; d >>= 32;
    fe_fold_nb(r, (uint)d);
    return r;
}
QG_FI fe fe_add(fe a, fe b) {
    fe r;
    qg_u64 c = 0;
    c += (qg_u64)a.v0 + b.v0; r.v0 = (uint)c; c >>= 32;
    c += (qg_u64)a.v1 + b.v1; r.v1 = (uint)c; c >>= 32;
    c += (qg_u64)a.v2 + b.v2; r.v2 = (uint)c; c >>= 32;
    c += (qg_u64)a.v3 + b.v3; r.v3 = (uint)c; c >>= 32;
    c += (qg_u64)a.v4 + b.v4; r.v4 = (uint)c; c >>= 32;
    c += (qg_u64)a.v5 + b.v5; r.v5 = (uint)c; c >>= 32;
    c += (qg_u64)a.v6 + b.v6; r.v6 = (uint)c; c >>= 32;
    c += (qg_u64)a.v7 + b.v7; r.v7 = (uint)c; c >>= 32;
    uint k = (uint)c;
    fe_fold(r, k);
    return r;
}
QG_FI fe fe_sub(fe a, fe b) {
    fe r; uint br = 0, t;
    t = a.v0 - b.v0; uint n0 = (a.v0 < b.v0) ? 1u : 0u; r.v0 = t - br; n0 |= (t < br) ? 1u : 0u; br = n0;
    t = a.v1 - b.v1; uint n1 = (a.v1 < b.v1) ? 1u : 0u; r.v1 = t - br; n1 |= (t < br) ? 1u : 0u; br = n1;
    t = a.v2 - b.v2; uint n2 = (a.v2 < b.v2) ? 1u : 0u; r.v2 = t - br; n2 |= (t < br) ? 1u : 0u; br = n2;
    t = a.v3 - b.v3; uint n3 = (a.v3 < b.v3) ? 1u : 0u; r.v3 = t - br; n3 |= (t < br) ? 1u : 0u; br = n3;
    t = a.v4 - b.v4; uint n4 = (a.v4 < b.v4) ? 1u : 0u; r.v4 = t - br; n4 |= (t < br) ? 1u : 0u; br = n4;
    t = a.v5 - b.v5; uint n5 = (a.v5 < b.v5) ? 1u : 0u; r.v5 = t - br; n5 |= (t < br) ? 1u : 0u; br = n5;
    t = a.v6 - b.v6; uint n6 = (a.v6 < b.v6) ? 1u : 0u; r.v6 = t - br; n6 |= (t < br) ? 1u : 0u; br = n6;
    t = a.v7 - b.v7; uint n7 = (a.v7 < b.v7) ? 1u : 0u; r.v7 = t - br; n7 |= (t < br) ? 1u : 0u; br = n7;
    if (br) fe_unfold(r, 1u);
    return r;
}

QG_FI fe fe_dbl(fe a) { return fe_add(a, a); }

// canonical value < p
QG_FI fe fe_norm(fe a) {
    qg_u64 d = (qg_u64)a.v0 + 977u; fe t; t.v0 = (uint)d; d >>= 32;
    d += (qg_u64)a.v1 + 1u; t.v1 = (uint)d; d >>= 32;
    d += a.v2; t.v2 = (uint)d; d >>= 32;
    d += a.v3; t.v3 = (uint)d; d >>= 32;
    d += a.v4; t.v4 = (uint)d; d >>= 32;
    d += a.v5; t.v5 = (uint)d; d >>= 32;
    d += a.v6; t.v6 = (uint)d; d >>= 32;
    d += a.v7; t.v7 = (uint)d; d >>= 32;
    return d ? t : a;                              // a + (2^256 - p) overflowed <=> a >= p
}

QG_FI fe fe_zero() { fe r; r.v0 = r.v1 = r.v2 = r.v3 = r.v4 = r.v5 = r.v6 = r.v7 = 0u; return r; }
QG_FI fe fe_one() { fe r = fe_zero(); r.v0 = 1u; return r; }

QG_DEV fe fe_sqrn(fe a, int n) { for (int i = 0; i < n; i++) a = fe_sqr(a); return a; }

QG_DEV fe fe_inv(fe a) {                                  // a^(p-2), libsecp256k1's addition chain
    fe x2 = fe_mul(fe_sqr(a), a);
    fe x3 = fe_mul(fe_sqr(x2), a);
    fe x6 = fe_mul(fe_sqrn(x3, 3), x3);
    fe x9 = fe_mul(fe_sqrn(x6, 3), x3);
    fe x11 = fe_mul(fe_sqrn(x9, 2), x2);
    fe x22 = fe_mul(fe_sqrn(x11, 11), x11);
    fe x44 = fe_mul(fe_sqrn(x22, 22), x22);
    fe x88 = fe_mul(fe_sqrn(x44, 44), x44);
    fe x176 = fe_mul(fe_sqrn(x88, 88), x88);
    fe x220 = fe_mul(fe_sqrn(x176, 44), x44);
    fe x223 = fe_mul(fe_sqrn(x220, 3), x3);
    fe t = fe_mul(fe_sqrn(x223, 23), x22);
    t = fe_mul(fe_sqrn(t, 5), a);
    t = fe_mul(fe_sqrn(t, 3), x2);
    return fe_mul(fe_sqrn(t, 2), a);
}


// ---- from a_inv.metal
// fe_inv_sg(a) = a^-1 mod p by safegcd (Bernstein-Yang divsteps, libsecp256k1 modinv32 algorithm):
// p = -0x3D1 - 4*2^30 + 65536*2^240 in signed 30-bit limbs, p^-1 mod 2^30 = 0x2DDACACF.

QG_FI int sg_divsteps_30(int zeta, uint f0, uint g0, int &tu, int &tv, int &tq, int &tr) {
    uint u = 1, v = 0, q = 0, r = 1, f = f0, g = g0;
    for (int i = 0; i < 30; i++) {
        uint c1 = (uint)(zeta >> 31), c2 = 0u - (g & 1u);
        uint x = (f ^ c1) - c1, y = (u ^ c1) - c1, z = (v ^ c1) - c1;
        g += x & c2; q += y & c2; r += z & c2;
        c1 &= c2;
        zeta = (zeta ^ (int)c1) - 1;
        f += g & c1; u += q & c1; v += r & c1;
        g >>= 1; u <<= 1; v <<= 1;
    }
    tu = (int)u; tv = (int)v; tq = (int)q; tr = (int)r;
    return zeta;
}

QG_DEV fe fe_inv_sg(fe a) {
    a = fe_norm(a);
    const int M30 = 0x3FFFFFFF;
    int g0 = (int)(a.v0 & 0x3FFFFFFFu);
    int g1 = (int)(((a.v0 >> 30) | (a.v1 << 2)) & 0x3FFFFFFFu);
    int g2 = (int)(((a.v1 >> 28) | (a.v2 << 4)) & 0x3FFFFFFFu);
    int g3 = (int)(((a.v2 >> 26) | (a.v3 << 6)) & 0x3FFFFFFFu);
    int g4 = (int)(((a.v3 >> 24) | (a.v4 << 8)) & 0x3FFFFFFFu);
    int g5 = (int)(((a.v4 >> 22) | (a.v5 << 10)) & 0x3FFFFFFFu);
    int g6 = (int)(((a.v5 >> 20) | (a.v6 << 12)) & 0x3FFFFFFFu);
    int g7 = (int)(((a.v6 >> 18) | (a.v7 << 14)) & 0x3FFFFFFFu);
    int g8 = (int)(a.v7 >> 16);
    int f0 = -0x3D1, f1 = -4, f2 = 0, f3 = 0, f4 = 0, f5 = 0, f6 = 0, f7 = 0, f8 = 65536;
    int d0 = 0; int d1 = 0; int d2 = 0; int d3 = 0; int d4 = 0; int d5 = 0; int d6 = 0; int d7 = 0; int d8 = 0;
    int e0 = 1; int e1 = 0; int e2 = 0; int e3 = 0; int e4 = 0; int e5 = 0; int e6 = 0; int e7 = 0; int e8 = 0;
    int zeta = -1;
    for (int it = 0; it < 20; it++) {
        int u, v, q, r;
        zeta = sg_divsteps_30(zeta, (uint)f0, (uint)g0, u, v, q, r);
        {
            int sd = d8 >> 31, se = e8 >> 31;
            int md = (u & sd) + (v & se), me = (q & sd) + (r & se);
            qg_i64 cd = (qg_i64)u * d0 + (qg_i64)v * e0, ce = (qg_i64)q * d0 + (qg_i64)r * e0;
            md -= (int)((0x2DDACACFu * (uint)cd + (uint)md) & 0x3FFFFFFFu);
            me -= (int)((0x2DDACACFu * (uint)ce + (uint)me) & 0x3FFFFFFFu);
            cd += (qg_i64)(-0x3D1) * md; ce += (qg_i64)(-0x3D1) * me;
            cd >>= 30; ce >>= 30;
            { int di = d1, ei = e1;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              cd -= (qg_i64)md * 4; ce -= (qg_i64)me * 4;
              d0 = (int)cd & M30; cd >>= 30; e0 = (int)ce & M30; ce >>= 30; }
            { int di = d2, ei = e2;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              d1 = (int)cd & M30; cd >>= 30; e1 = (int)ce & M30; ce >>= 30; }
            { int di = d3, ei = e3;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              d2 = (int)cd & M30; cd >>= 30; e2 = (int)ce & M30; ce >>= 30; }
            { int di = d4, ei = e4;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              d3 = (int)cd & M30; cd >>= 30; e3 = (int)ce & M30; ce >>= 30; }
            { int di = d5, ei = e5;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              d4 = (int)cd & M30; cd >>= 30; e4 = (int)ce & M30; ce >>= 30; }
            { int di = d6, ei = e6;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              d5 = (int)cd & M30; cd >>= 30; e5 = (int)ce & M30; ce >>= 30; }
            { int di = d7, ei = e7;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              d6 = (int)cd & M30; cd >>= 30; e6 = (int)ce & M30; ce >>= 30; }
            { int di = d8, ei = e8;
              cd += (qg_i64)u * di + (qg_i64)v * ei; ce += (qg_i64)q * di + (qg_i64)r * ei;
              cd += (qg_i64)md * 65536; ce += (qg_i64)me * 65536;
              d7 = (int)cd & M30; cd >>= 30; e7 = (int)ce & M30; ce >>= 30; }
            d8 = (int)cd; e8 = (int)ce;
        }
        {
            qg_i64 cf = (qg_i64)u * f0 + (qg_i64)v * g0, cg = (qg_i64)q * f0 + (qg_i64)r * g0;
            cf >>= 30; cg >>= 30;
            { int fi = f1, gi = g1;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f0 = (int)cf & M30; cf >>= 30; g0 = (int)cg & M30; cg >>= 30; }
            { int fi = f2, gi = g2;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f1 = (int)cf & M30; cf >>= 30; g1 = (int)cg & M30; cg >>= 30; }
            { int fi = f3, gi = g3;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f2 = (int)cf & M30; cf >>= 30; g2 = (int)cg & M30; cg >>= 30; }
            { int fi = f4, gi = g4;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f3 = (int)cf & M30; cf >>= 30; g3 = (int)cg & M30; cg >>= 30; }
            { int fi = f5, gi = g5;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f4 = (int)cf & M30; cf >>= 30; g4 = (int)cg & M30; cg >>= 30; }
            { int fi = f6, gi = g6;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f5 = (int)cf & M30; cf >>= 30; g5 = (int)cg & M30; cg >>= 30; }
            { int fi = f7, gi = g7;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f6 = (int)cf & M30; cf >>= 30; g6 = (int)cg & M30; cg >>= 30; }
            { int fi = f8, gi = g8;
              cf += (qg_i64)u * fi + (qg_i64)v * gi; cg += (qg_i64)q * fi + (qg_i64)r * gi;
              f7 = (int)cf & M30; cf >>= 30; g7 = (int)cg & M30; cg >>= 30; }
            f8 = (int)cf; g8 = (int)cg;
        }
    }
    {
        int ca = d8 >> 31;
        d0 += -0x3D1 & ca; d1 += -4 & ca; d8 += 65536 & ca;
        int cn = f8 >> 31;
        d0 = (d0 ^ cn) - cn;
        d1 = (d1 ^ cn) - cn;
        d2 = (d2 ^ cn) - cn;
        d3 = (d3 ^ cn) - cn;
        d4 = (d4 ^ cn) - cn;
        d5 = (d5 ^ cn) - cn;
        d6 = (d6 ^ cn) - cn;
        d7 = (d7 ^ cn) - cn;
        d8 = (d8 ^ cn) - cn;
        d1 += d0 >> 30; d0 &= M30;
        d2 += d1 >> 30; d1 &= M30;
        d3 += d2 >> 30; d2 &= M30;
        d4 += d3 >> 30; d3 &= M30;
        d5 += d4 >> 30; d4 &= M30;
        d6 += d5 >> 30; d5 &= M30;
        d7 += d6 >> 30; d6 &= M30;
        d8 += d7 >> 30; d7 &= M30;
        ca = d8 >> 31;
        d0 += -0x3D1 & ca; d1 += -4 & ca; d8 += 65536 & ca;
        d1 += d0 >> 30; d0 &= M30;
        d2 += d1 >> 30; d1 &= M30;
        d3 += d2 >> 30; d2 &= M30;
        d4 += d3 >> 30; d3 &= M30;
        d5 += d4 >> 30; d4 &= M30;
        d6 += d5 >> 30; d5 &= M30;
        d7 += d6 >> 30; d6 &= M30;
        d8 += d7 >> 30; d7 &= M30;
    }
    fe r;
    r.v0 = (uint)d0 | ((uint)d1 << 30);
    r.v1 = ((uint)d1 >> 2) | ((uint)d2 << 28);
    r.v2 = ((uint)d2 >> 4) | ((uint)d3 << 26);
    r.v3 = ((uint)d3 >> 6) | ((uint)d4 << 24);
    r.v4 = ((uint)d4 >> 8) | ((uint)d5 << 22);
    r.v5 = ((uint)d5 >> 10) | ((uint)d6 << 20);
    r.v6 = ((uint)d6 >> 12) | ((uint)d7 << 18);
    r.v7 = ((uint)d7 >> 14) | ((uint)d8 << 16);
    return r;
}

// ---- from b_sha.metal
// SHA-256 compression, fully unrolled, message words passed by value so constant words fold.
// Rotations via a funnel shift (qg_rotr). Maj is folded into the rounds as b ^ (ab & bc).
#define SHA_ROTR(x, n) qg_rotr((x), (n))
#define SHA_S0(x) SHA_ROTR((x) ^ SHA_ROTR((x) ^ SHA_ROTR((x), 9), 11), 2)      // = ROTR2^ROTR13^ROTR22
#define SHA_S1(x) SHA_ROTR((x) ^ SHA_ROTR((x) ^ SHA_ROTR((x), 14), 5), 6)      // = ROTR6^ROTR11^ROTR25 (0.8% faster)
#define SHA_s0(x) (SHA_ROTR(x, 7) ^ SHA_ROTR(x, 18) ^ ((x) >> 3))
#define SHA_s1(x) (SHA_ROTR(x, 17) ^ SHA_ROTR(x, 19) ^ ((x) >> 10))
#define SHA_CH(e, f, g) ((g) ^ ((e) & ((f) ^ (g))))

struct shst { uint a, b, c, d, e, f, g, h; };

QG_CONST shst SHA_IV = {0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au,
                        0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u};

QG_FI shst sha_blk(shst s, uint w0, uint w1, uint w2, uint w3, uint w4, uint w5, uint w6, uint w7, uint w8, uint w9, uint w10, uint w11, uint w12, uint w13, uint w14, uint w15) {
    uint a = s.a, b = s.b, c = s.c, d = s.d, e = s.e, f = s.f, g = s.g, h = s.h;
    uint bc = b ^ c, ab;
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0x428a2f98u + w0; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0x71374491u + w1; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0xb5c0fbcfu + w2; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0xe9b5dba5u + w3; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0x3956c25bu + w4; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0x59f111f1u + w5; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0x923f82a4u + w6; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0xab1c5ed5u + w7; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0xd807aa98u + w8; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0x12835b01u + w9; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0x243185beu + w10; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0x550c7dc3u + w11; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0x72be5d74u + w12; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0x80deb1feu + w13; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0x9bdc06a7u + w14; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0xc19bf174u + w15; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    w0 += SHA_s1(w14) + w9 + SHA_s0(w1);
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0xe49b69c1u + w0; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    w1 += SHA_s1(w15) + w10 + SHA_s0(w2);
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0xefbe4786u + w1; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    w2 += SHA_s1(w0) + w11 + SHA_s0(w3);
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0x0fc19dc6u + w2; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    w3 += SHA_s1(w1) + w12 + SHA_s0(w4);
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0x240ca1ccu + w3; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    w4 += SHA_s1(w2) + w13 + SHA_s0(w5);
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0x2de92c6fu + w4; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    w5 += SHA_s1(w3) + w14 + SHA_s0(w6);
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0x4a7484aau + w5; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    w6 += SHA_s1(w4) + w15 + SHA_s0(w7);
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0x5cb0a9dcu + w6; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    w7 += SHA_s1(w5) + w0 + SHA_s0(w8);
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0x76f988dau + w7; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    w8 += SHA_s1(w6) + w1 + SHA_s0(w9);
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0x983e5152u + w8; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    w9 += SHA_s1(w7) + w2 + SHA_s0(w10);
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0xa831c66du + w9; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    w10 += SHA_s1(w8) + w3 + SHA_s0(w11);
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0xb00327c8u + w10; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    w11 += SHA_s1(w9) + w4 + SHA_s0(w12);
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0xbf597fc7u + w11; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    w12 += SHA_s1(w10) + w5 + SHA_s0(w13);
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0xc6e00bf3u + w12; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    w13 += SHA_s1(w11) + w6 + SHA_s0(w14);
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0xd5a79147u + w13; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    w14 += SHA_s1(w12) + w7 + SHA_s0(w15);
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0x06ca6351u + w14; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    w15 += SHA_s1(w13) + w8 + SHA_s0(w0);
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0x14292967u + w15; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    w0 += SHA_s1(w14) + w9 + SHA_s0(w1);
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0x27b70a85u + w0; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    w1 += SHA_s1(w15) + w10 + SHA_s0(w2);
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0x2e1b2138u + w1; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    w2 += SHA_s1(w0) + w11 + SHA_s0(w3);
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0x4d2c6dfcu + w2; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    w3 += SHA_s1(w1) + w12 + SHA_s0(w4);
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0x53380d13u + w3; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    w4 += SHA_s1(w2) + w13 + SHA_s0(w5);
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0x650a7354u + w4; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    w5 += SHA_s1(w3) + w14 + SHA_s0(w6);
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0x766a0abbu + w5; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    w6 += SHA_s1(w4) + w15 + SHA_s0(w7);
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0x81c2c92eu + w6; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    w7 += SHA_s1(w5) + w0 + SHA_s0(w8);
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0x92722c85u + w7; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    w8 += SHA_s1(w6) + w1 + SHA_s0(w9);
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0xa2bfe8a1u + w8; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    w9 += SHA_s1(w7) + w2 + SHA_s0(w10);
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0xa81a664bu + w9; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    w10 += SHA_s1(w8) + w3 + SHA_s0(w11);
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0xc24b8b70u + w10; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    w11 += SHA_s1(w9) + w4 + SHA_s0(w12);
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0xc76c51a3u + w11; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    w12 += SHA_s1(w10) + w5 + SHA_s0(w13);
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0xd192e819u + w12; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    w13 += SHA_s1(w11) + w6 + SHA_s0(w14);
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0xd6990624u + w13; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    w14 += SHA_s1(w12) + w7 + SHA_s0(w15);
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0xf40e3585u + w14; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    w15 += SHA_s1(w13) + w8 + SHA_s0(w0);
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0x106aa070u + w15; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    w0 += SHA_s1(w14) + w9 + SHA_s0(w1);
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0x19a4c116u + w0; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    w1 += SHA_s1(w15) + w10 + SHA_s0(w2);
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0x1e376c08u + w1; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    w2 += SHA_s1(w0) + w11 + SHA_s0(w3);
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0x2748774cu + w2; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    w3 += SHA_s1(w1) + w12 + SHA_s0(w4);
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0x34b0bcb5u + w3; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    w4 += SHA_s1(w2) + w13 + SHA_s0(w5);
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0x391c0cb3u + w4; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    w5 += SHA_s1(w3) + w14 + SHA_s0(w6);
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0x4ed8aa4au + w5; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    w6 += SHA_s1(w4) + w15 + SHA_s0(w7);
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0x5b9cca4fu + w6; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    w7 += SHA_s1(w5) + w0 + SHA_s0(w8);
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0x682e6ff3u + w7; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    w8 += SHA_s1(w6) + w1 + SHA_s0(w9);
    { uint t1 = h + SHA_S1(e) + SHA_CH(e, f, g) + 0x748f82eeu + w8; d += t1; ab = a ^ b; h = t1 + SHA_S0(a) + (b ^ (ab & bc)); bc = ab; }
    w9 += SHA_s1(w7) + w2 + SHA_s0(w10);
    { uint t1 = g + SHA_S1(d) + SHA_CH(d, e, f) + 0x78a5636fu + w9; c += t1; ab = h ^ a; g = t1 + SHA_S0(h) + (a ^ (ab & bc)); bc = ab; }
    w10 += SHA_s1(w8) + w3 + SHA_s0(w11);
    { uint t1 = f + SHA_S1(c) + SHA_CH(c, d, e) + 0x84c87814u + w10; b += t1; ab = g ^ h; f = t1 + SHA_S0(g) + (h ^ (ab & bc)); bc = ab; }
    w11 += SHA_s1(w9) + w4 + SHA_s0(w12);
    { uint t1 = e + SHA_S1(b) + SHA_CH(b, c, d) + 0x8cc70208u + w11; a += t1; ab = f ^ g; e = t1 + SHA_S0(f) + (g ^ (ab & bc)); bc = ab; }
    w12 += SHA_s1(w10) + w5 + SHA_s0(w13);
    { uint t1 = d + SHA_S1(a) + SHA_CH(a, b, c) + 0x90befffau + w12; h += t1; ab = e ^ f; d = t1 + SHA_S0(e) + (f ^ (ab & bc)); bc = ab; }
    w13 += SHA_s1(w11) + w6 + SHA_s0(w14);
    { uint t1 = c + SHA_S1(h) + SHA_CH(h, a, b) + 0xa4506cebu + w13; g += t1; ab = d ^ e; c = t1 + SHA_S0(d) + (e ^ (ab & bc)); bc = ab; }
    w14 += SHA_s1(w12) + w7 + SHA_s0(w15);
    { uint t1 = b + SHA_S1(g) + SHA_CH(g, h, a) + 0xbef9a3f7u + w14; f += t1; ab = c ^ d; b = t1 + SHA_S0(c) + (d ^ (ab & bc)); bc = ab; }
    w15 += SHA_s1(w13) + w8 + SHA_s0(w0);
    { uint t1 = a + SHA_S1(f) + SHA_CH(f, g, h) + 0xc67178f2u + w15; e += t1; ab = b ^ c; a = t1 + SHA_S0(b) + (c ^ (ab & bc)); bc = ab; }
    shst r; r.a = s.a + a; r.b = s.b + b; r.c = s.c + c; r.d = s.d + d;
    r.e = s.e + e; r.f = s.f + f; r.g = s.g + g; r.h = s.h + h;
    return r;
}
