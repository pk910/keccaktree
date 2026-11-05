/* AArch64 Advanced SIMD: 2 nodes in parallel, one node per 64-bit lane of a
 * q register; the 25-lane state fits the 32 vector registers.
 * Compiled twice: KT_SHA3 (FEAT_SHA3, ARMv8.2+, all Apple M-series, Graviton3+,
 * Neoverse V1/N2+) maps theta/rho/chi onto EOR3 / RAX1 / XAR / BCAX, which
 * makes every lane update of theta+rho a single XAR and every chi a BCAX. */
#include <arm_neon.h>
#include "keccaktree.h"
#include "keccak_rc.h"

typedef uint64x2_t V;
#define XOR(a, b) veorq_u64((a), (b))
#ifdef KT_SHA3
#define XOR3(a, b, c) veor3q_u64((a), (b), (c))
#define ROL1XOR(a, b) vrax1q_u64((a), (b))
#define XORROL(a, b, n) vxarq_u64((a), (b), 64 - (n))
#define ROL(a, n) vxarq_u64((a), vdupq_n_u64(0), 64 - (n))
#define CHI(a, b, c) vbcaxq_u64((a), (c), (b))
#define FN keccaktree_keccak256_sha3_x2
#else
#define XOR3(a, b, c) veorq_u64(veorq_u64((a), (b)), (c))
#define ROL(a, n) vsriq_n_u64(vshlq_n_u64((a), (n)), (a), 64 - (n))
#define ROL1XOR(a, b) veorq_u64((a), ROL((b), 1))
#define XORROL(a, b, n) ROL(veorq_u64((a), (b)), (n))
#define CHI(a, b, c) veorq_u64((a), vbicq_u64((c), (b)))
#define FN keccaktree_keccak256_neon_x2
#endif
#define KC(x) vdupq_n_u64((uint64_t)(x))
#define IOTA(a, i) veorq_u64((a), vdupq_n_u64(KECCAK_RC[i]))

static __attribute__((noinline)) void x2_batch(unsigned char* output, const unsigned char* input,
                                                           unsigned n) {
    const uint64_t* p = (const uint64_t*)input;
    V z = vdupq_n_u64(0);
    V p0 = vld1q_u64(p), p1 = vld1q_u64(p + 2), p2 = vld1q_u64(p + 4), p3 = vld1q_u64(p + 6);
    V q0 = n > 1 ? vld1q_u64(p + 8) : z, q1 = n > 1 ? vld1q_u64(p + 10) : z;
    V q2 = n > 1 ? vld1q_u64(p + 12) : z, q3 = n > 1 ? vld1q_u64(p + 14) : z;
    V a0 = vzip1q_u64(p0, q0), a1 = vzip2q_u64(p0, q0);
    V a2 = vzip1q_u64(p1, q1), a3 = vzip2q_u64(p1, q1);
    V a4 = vzip1q_u64(p2, q2), a5 = vzip2q_u64(p2, q2);
    V a6 = vzip1q_u64(p3, q3), a7 = vzip2q_u64(p3, q3);
    V o0, o1, o2, o3;
#include "keccak256_core.inc"
    uint64_t* d = (uint64_t*)output;
    vst1q_u64(d, vzip1q_u64(o0, o1));
    vst1q_u64(d + 2, vzip1q_u64(o2, o3));
    if (n > 1) {
        vst1q_u64(d + 4, vzip2q_u64(o0, o1));
        vst1q_u64(d + 6, vzip2q_u64(o2, o3));
    }
}

void FN(unsigned char* output, const unsigned char* input, uint64_t count) {
    while (count >= 2) {
        x2_batch(output, input, 2);
        input += 2 * 64;
        output += 2 * 32;
        count -= 2;
    }
    if (count) x2_batch(output, input, 1);
}
