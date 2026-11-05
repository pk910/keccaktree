/* AVX2 (and AVX-512VL) 4 nodes in parallel, one node per 64-bit lane of a ymm.
 * Plain AVX2 has no 64-bit rotate and no ternary logic, so ROL costs 3 ops
 * (1 for rot 8/56 via vpshufb) and chi costs 2; the state does not fit
 * the 16 ymm registers and spills to the stack.
 * Compiled twice: KT_AVX512VL selects vprolq/vpternlogq on ymm (32 regs). */
#include <immintrin.h>
#include "keccaktree.h"
#include "keccak_rc.h"

typedef __m256i V;
#define XOR(a, b) _mm256_xor_si256((a), (b))

#ifdef KT_AVX512VL
#define XOR3(a, b, c) _mm256_ternarylogic_epi64((a), (b), (c), 0x96)
#define ROL(a, n) _mm256_rol_epi64((a), (n))
#define CHI(a, b, c) _mm256_ternarylogic_epi64((a), (b), (c), 0xD2)
#define FN keccaktree_keccak256_avx512vl_x4
#define KT_CORE "keccak256_core_tl.inc"
#else
#define XOR3(a, b, c) _mm256_xor_si256(_mm256_xor_si256((a), (b)), (c))
#define CHI(a, b, c) _mm256_xor_si256((a), _mm256_andnot_si256((b), (c)))
#define FN keccaktree_keccak256_avx2_x4
#define KT_CORE "keccak256_core.inc"
static inline __attribute__((always_inline)) __m256i rol_avx2(__m256i a, int n) {
    if (n == 8)
        return _mm256_shuffle_epi8(a, _mm256_setr_epi8(7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14, 7, 0,
                                                       1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14));
    if (n == 56)
        return _mm256_shuffle_epi8(a, _mm256_setr_epi8(1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8, 1, 2,
                                                       3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8));
    if (n == 1) return _mm256_or_si256(_mm256_add_epi64(a, a), _mm256_srli_epi64(a, 63));
    return _mm256_or_si256(_mm256_slli_epi64(a, n), _mm256_srli_epi64(a, 64 - n));
}
#define ROL(a, n) rol_avx2((a), (n))
#endif
#define ROL1XOR(a, b) XOR((a), ROL((b), 1))
#define XORROL(a, b, n) ROL(XOR((a), (b)), (n))
#define KC(x) _mm256_set1_epi64x((long long)(x))
#define IOTA(a, i) XOR((a), _mm256_set1_epi64x((long long)KECCAK_RC[i]))

static inline __attribute__((always_inline)) void x4_batch(unsigned char* output, const unsigned char* input,
                                                           unsigned n) {
    V z = _mm256_setzero_si256();
    V l0 = _mm256_loadu_si256((const __m256i*)(input + 0));
    V h0 = _mm256_loadu_si256((const __m256i*)(input + 32));
    V l1 = n > 1 ? _mm256_loadu_si256((const __m256i*)(input + 64)) : z;
    V h1 = n > 1 ? _mm256_loadu_si256((const __m256i*)(input + 96)) : z;
    V l2 = n > 2 ? _mm256_loadu_si256((const __m256i*)(input + 128)) : z;
    V h2 = n > 2 ? _mm256_loadu_si256((const __m256i*)(input + 160)) : z;
    V l3 = n > 3 ? _mm256_loadu_si256((const __m256i*)(input + 192)) : z;
    V h3 = n > 3 ? _mm256_loadu_si256((const __m256i*)(input + 224)) : z;
    /* two 4x4 qword transposes */
    V t0 = _mm256_unpacklo_epi64(l0, l1), t1 = _mm256_unpackhi_epi64(l0, l1);
    V t2 = _mm256_unpacklo_epi64(l2, l3), t3 = _mm256_unpackhi_epi64(l2, l3);
    V a0 = _mm256_permute2x128_si256(t0, t2, 0x20), a2 = _mm256_permute2x128_si256(t0, t2, 0x31);
    V a1 = _mm256_permute2x128_si256(t1, t3, 0x20), a3 = _mm256_permute2x128_si256(t1, t3, 0x31);
    t0 = _mm256_unpacklo_epi64(h0, h1); t1 = _mm256_unpackhi_epi64(h0, h1);
    t2 = _mm256_unpacklo_epi64(h2, h3); t3 = _mm256_unpackhi_epi64(h2, h3);
    V a4 = _mm256_permute2x128_si256(t0, t2, 0x20), a6 = _mm256_permute2x128_si256(t0, t2, 0x31);
    V a5 = _mm256_permute2x128_si256(t1, t3, 0x20), a7 = _mm256_permute2x128_si256(t1, t3, 0x31);
    V o0, o1, o2, o3;
#include KT_CORE
    t0 = _mm256_unpacklo_epi64(o0, o1); t1 = _mm256_unpackhi_epi64(o0, o1);
    t2 = _mm256_unpacklo_epi64(o2, o3); t3 = _mm256_unpackhi_epi64(o2, o3);
    _mm256_storeu_si256((__m256i*)(output + 0), _mm256_permute2x128_si256(t0, t2, 0x20));
    if (n > 1) _mm256_storeu_si256((__m256i*)(output + 32), _mm256_permute2x128_si256(t1, t3, 0x20));
    if (n > 2) _mm256_storeu_si256((__m256i*)(output + 64), _mm256_permute2x128_si256(t0, t2, 0x31));
    if (n > 3) _mm256_storeu_si256((__m256i*)(output + 96), _mm256_permute2x128_si256(t1, t3, 0x31));
}

void FN(unsigned char* output, const unsigned char* input, uint64_t count) {
    while (count >= 4) {
        x4_batch(output, input, 4);
        input += 4 * 64;
        output += 4 * 32;
        count -= 4;
    }
    if (count) x4_batch(output, input, (unsigned)count);
}
