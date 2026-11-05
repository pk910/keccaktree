/* AArch64 kernels for Arm Ltd cores (Neoverse, Cortex-A7xx/X):
 *
 *  scalar_x1  (KT_HV=0 KT_HS=1)          one node in the integer ALUs
 *  sha3_x3    (KT_HV=1 KT_HS=1 KT_SHA3)  the sha3_x2 stream (2 nodes) and one
 *                                         scalar node interleaved round by
 *                                         round, so the integer ALUs work
 *                                         while the vector pipes are busy
 *
 * The scalar stream uses lazy rotations (tools/gen_hybrid.py): rho is free
 * because EOR/BIC rotate their second operand in the same instruction. That
 * holds on Arm's cores (Neoverse N2: scalar_x1 is 1.5x the plain-rotation C
 * code, sha3_x3 is 1.26x sha3_x2) but not on Apple's, where a rotated operand
 * costs extra and both kernels lose to sha3_x2; keccaktree.c dispatches on
 * the MIDR implementer accordingly. Counts below 3 go to scalar_x1. */
#include <arm_neon.h>
#include "keccaktree.h"
#include "keccak_rc.h"
#include "keccak_lazy_rc.h"

typedef uint64x2_t V;
#define XOR(a, b) veorq_u64((a), (b))
#ifdef KT_SHA3
#define XOR3(a, b, c) veor3q_u64((a), (b), (c))
#define ROL1XOR(a, b) vrax1q_u64((a), (b))
#define XORROL(a, b, n) vxarq_u64((a), (b), 64 - (n))
#define ROL(a, n) vxarq_u64((a), vdupq_n_u64(0), 64 - (n))
#define CHI(a, b, c) vbcaxq_u64((a), (c), (b))
#else
#define XOR3(a, b, c) veorq_u64(veorq_u64((a), (b)), (c))
#define ROL(a, n) vsriq_n_u64(vshlq_n_u64((a), (n)), (a), 64 - (n))
#define ROL1XOR(a, b) veorq_u64((a), ROL((b), 1))
#define XORROL(a, b, n) ROL(veorq_u64((a), (b)), (n))
#define CHI(a, b, c) veorq_u64((a), vbicq_u64((c), (b)))
#endif
#define KC(x) vdupq_n_u64((uint64_t)(x))
#define IOTA(a, i) veorq_u64((a), vdupq_n_u64(KECCAK_RC[i]))

#define SROL(x, n) (((x) << (n)) | ((x) >> (64 - (n))))
/* keeps an intermediate in a register so the compiler does not reassociate
 * an EOR chain (which would cost explicit RORs); no instruction emitted */
#define SBAR(x) __asm__("" : "+r"(x))

#define WIDTH (2 * KT_HV + KT_HS)

#define VLOAD(i)                                                                                  \
    V v##i##_a0, v##i##_a1, v##i##_a2, v##i##_a3, v##i##_a4, v##i##_a5, v##i##_a6, v##i##_a7;     \
    V v##i##_o0, v##i##_o1, v##i##_o2, v##i##_o3;                                                 \
    {                                                                                             \
        const uint64_t* p = (const uint64_t*)(input + 128 * (i));                                 \
        V p0 = vld1q_u64(p), p1 = vld1q_u64(p + 2), p2 = vld1q_u64(p + 4), p3 = vld1q_u64(p + 6); \
        V q0 = vld1q_u64(p + 8), q1 = vld1q_u64(p + 10), q2 = vld1q_u64(p + 12);                  \
        V q3 = vld1q_u64(p + 14);                                                                 \
        v##i##_a0 = vzip1q_u64(p0, q0), v##i##_a1 = vzip2q_u64(p0, q0);                           \
        v##i##_a2 = vzip1q_u64(p1, q1), v##i##_a3 = vzip2q_u64(p1, q1);                           \
        v##i##_a4 = vzip1q_u64(p2, q2), v##i##_a5 = vzip2q_u64(p2, q2);                           \
        v##i##_a6 = vzip1q_u64(p3, q3), v##i##_a7 = vzip2q_u64(p3, q3);                           \
    }
#define VSTORE(i)                                                \
    {                                                            \
        uint64_t* d = (uint64_t*)(output + 64 * (i));            \
        vst1q_u64(d, vzip1q_u64(v##i##_o0, v##i##_o1));          \
        vst1q_u64(d + 2, vzip1q_u64(v##i##_o2, v##i##_o3));      \
        vst1q_u64(d + 4, vzip2q_u64(v##i##_o0, v##i##_o1));      \
        vst1q_u64(d + 6, vzip2q_u64(v##i##_o2, v##i##_o3));      \
    }
#define SLOAD(j)                                                                         \
    const uint64_t* sp##j = (const uint64_t*)(input + 128 * KT_HV + 64 * (j));           \
    uint64_t s##j##_a0 = sp##j[0], s##j##_a1 = sp##j[1], s##j##_a2 = sp##j[2];           \
    uint64_t s##j##_a3 = sp##j[3], s##j##_a4 = sp##j[4], s##j##_a5 = sp##j[5];           \
    uint64_t s##j##_a6 = sp##j[6], s##j##_a7 = sp##j[7];                                 \
    uint64_t s##j##_o0, s##j##_o1, s##j##_o2, s##j##_o3;
#define SSTORE(j)                                                       \
    {                                                                   \
        uint64_t* d = (uint64_t*)(output + 64 * KT_HV + 32 * (j));      \
        d[0] = s##j##_o0, d[1] = s##j##_o1, d[2] = s##j##_o2, d[3] = s##j##_o3; \
    }

static __attribute__((noinline)) void batch(unsigned char* output, const unsigned char* input) {
    /* opaque to the optimiser, so the constants are loaded from the table
     * (one LDR) instead of being built with MOV/MOVK */
    const uint64_t* lrc = KT_LAZY_RC;
    SBAR(lrc);
#if KT_HV > 0
    VLOAD(0)
#endif
    SLOAD(0)
#if KT_HV == 0 && KT_HS == 1
#include "hybrid/arm_v0s1.inc"
#elif KT_HV == 1 && KT_HS == 1
#include "hybrid/arm_v1s1.inc"
#else
#error unsupported KT_HV/KT_HS
#endif
#if KT_HV > 0
    VSTORE(0)
#endif
    SSTORE(0)
}

void FN(unsigned char* output, const unsigned char* input, uint64_t count) {
    while (count >= WIDTH) {
        batch(output, input);
        input += WIDTH * 64;
        output += WIDTH * 32;
        count -= WIDTH;
    }
#if WIDTH > 1
    /* a 2-node vector batch takes as long as 2 scalar nodes on Neoverse N2 */
    if (count) keccaktree_keccak256_scalar_x1(output, input, count);
#endif
}
