/* AVX-512F: 8 nodes in parallel, one node per 64-bit lane of a zmm register.
 * The whole 25-lane state + theta temporaries fit the 32 zmm registers, and
 * vprolq / vpternlogq give single-instruction rotate, 3-way XOR and chi. */
#include <immintrin.h>
#include "keccaktree.h"
#include "keccak_rc.h"
#ifndef KT_CORE
#define KT_CORE "keccak256_core_tl.inc"
#endif

typedef __m512i V;
#define XOR(a, b) _mm512_xor_si512((a), (b))
#define XOR3(a, b, c) _mm512_ternarylogic_epi64((a), (b), (c), 0x96)
#define ROL(a, n) _mm512_rol_epi64((a), (n))
#define ROL1XOR(a, b) _mm512_xor_si512((a), _mm512_rol_epi64((b), 1))
#define XORROL(a, b, n) _mm512_rol_epi64(_mm512_xor_si512((a), (b)), (n))
#define CHI(a, b, c) _mm512_ternarylogic_epi64((a), (b), (c), 0xD2)
#define KC(x) _mm512_set1_epi64((long long)(x))
#define IOTA(a, i) _mm512_xor_si512((a), _mm512_set1_epi64((long long)KECCAK_RC[i]))

static inline __attribute__((always_inline)) void x8_batch(unsigned char* output, const unsigned char* input,
                                                           unsigned n) {
    V r0, r1, r2, r3, r4, r5, r6, r7;
    if (n == 8) {
        r0 = _mm512_loadu_si512(input + 0 * 64);
        r1 = _mm512_loadu_si512(input + 1 * 64);
        r2 = _mm512_loadu_si512(input + 2 * 64);
        r3 = _mm512_loadu_si512(input + 3 * 64);
        r4 = _mm512_loadu_si512(input + 4 * 64);
        r5 = _mm512_loadu_si512(input + 5 * 64);
        r6 = _mm512_loadu_si512(input + 6 * 64);
        r7 = _mm512_loadu_si512(input + 7 * 64);
    } else {
        /* masked loads never fault on masked-off lanes */
#define LDM(i) _mm512_maskz_loadu_epi64((__mmask8)((i) < n ? 0xFF : 0), input + ((i) < n ? (i) : 0) * 64)
        r0 = LDM(0); r1 = LDM(1); r2 = LDM(2); r3 = LDM(3);
        r4 = LDM(4); r5 = LDM(5); r6 = LDM(6); r7 = LDM(7);
#undef LDM
    }
    /* 8x8 qword transpose: a_j = word j of nodes 0..7 */
    V t0 = _mm512_unpacklo_epi64(r0, r1), t1 = _mm512_unpackhi_epi64(r0, r1);
    V t2 = _mm512_unpacklo_epi64(r2, r3), t3 = _mm512_unpackhi_epi64(r2, r3);
    V t4 = _mm512_unpacklo_epi64(r4, r5), t5 = _mm512_unpackhi_epi64(r4, r5);
    V t6 = _mm512_unpacklo_epi64(r6, r7), t7 = _mm512_unpackhi_epi64(r6, r7);
    V u0 = _mm512_shuffle_i64x2(t0, t2, 0x88), u1 = _mm512_shuffle_i64x2(t0, t2, 0xDD);
    V u2 = _mm512_shuffle_i64x2(t1, t3, 0x88), u3 = _mm512_shuffle_i64x2(t1, t3, 0xDD);
    V u4 = _mm512_shuffle_i64x2(t4, t6, 0x88), u5 = _mm512_shuffle_i64x2(t4, t6, 0xDD);
    V u6 = _mm512_shuffle_i64x2(t5, t7, 0x88), u7 = _mm512_shuffle_i64x2(t5, t7, 0xDD);
    V a0 = _mm512_shuffle_i64x2(u0, u4, 0x88), a4 = _mm512_shuffle_i64x2(u0, u4, 0xDD);
    V a2 = _mm512_shuffle_i64x2(u1, u5, 0x88), a6 = _mm512_shuffle_i64x2(u1, u5, 0xDD);
    V a1 = _mm512_shuffle_i64x2(u2, u6, 0x88), a5 = _mm512_shuffle_i64x2(u2, u6, 0xDD);
    V a3 = _mm512_shuffle_i64x2(u3, u7, 0x88), a7 = _mm512_shuffle_i64x2(u3, u7, 0xDD);
    V o0, o1, o2, o3;
#include KT_CORE
    /* 4x8 transpose back: two 32-byte digests per zmm */
    V q0 = _mm512_unpacklo_epi64(o0, o1), q1 = _mm512_unpackhi_epi64(o0, o1);
    V q2 = _mm512_unpacklo_epi64(o2, o3), q3 = _mm512_unpackhi_epi64(o2, o3);
    const V lo = _mm512_set_epi64(11, 10, 3, 2, 9, 8, 1, 0);
    const V hi = _mm512_set_epi64(15, 14, 7, 6, 13, 12, 5, 4);
    V m0 = _mm512_permutex2var_epi64(q0, lo, q2); /* nodes 0,2 */
    V m1 = _mm512_permutex2var_epi64(q1, lo, q3); /* nodes 1,3 */
    V m2 = _mm512_permutex2var_epi64(q0, hi, q2); /* nodes 4,6 */
    V m3 = _mm512_permutex2var_epi64(q1, hi, q3); /* nodes 5,7 */
    V d01 = _mm512_shuffle_i64x2(m0, m1, 0x44), d23 = _mm512_shuffle_i64x2(m0, m1, 0xEE);
    V d45 = _mm512_shuffle_i64x2(m2, m3, 0x44), d67 = _mm512_shuffle_i64x2(m2, m3, 0xEE);
    if (n == 8) {
        _mm512_storeu_si512(output + 0 * 64, d01);
        _mm512_storeu_si512(output + 1 * 64, d23);
        _mm512_storeu_si512(output + 2 * 64, d45);
        _mm512_storeu_si512(output + 3 * 64, d67);
    } else {
#define STM(k, v)                                                                    \
    do {                                                                             \
        unsigned m = (2 * (k) < n ? 0x0F : 0) | (2 * (k) + 1 < n ? 0xF0 : 0);         \
        if (m) _mm512_mask_storeu_epi64(output + (k) * 64, (__mmask8)m, (v));        \
    } while (0)
        STM(0, d01); STM(1, d23); STM(2, d45); STM(3, d67);
#undef STM
    }
}

void keccaktree_keccak256_avx512_x8(unsigned char* output, const unsigned char* input, uint64_t count) {
    while (count >= 8) {
        x8_batch(output, input, 8);
        input += 8 * 64;
        output += 8 * 32;
        count -= 8;
    }
    if (count) x8_batch(output, input, (unsigned)count);
}
