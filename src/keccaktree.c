/* Runtime dispatch, same contract as hashtree.c */
#include "keccaktree.h"

#ifdef __x86_64__
#include <cpuid.h>
#endif
#if defined(__aarch64__) && defined(__linux__)
#include <asm/hwcap.h>
#include <sys/auxv.h>
#endif

static void init_and_hash(unsigned char* output, const unsigned char* input, uint64_t count);
static keccaktree_hash_fcn hash_ptr = init_and_hash;

#ifdef __x86_64__
static uint64_t xgetbv0(void) {
    uint32_t lo, hi;
    __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
    return ((uint64_t)hi << 32) | lo;
}
#endif

static keccaktree_hash_fcn keccaktree_detect(void) {
#ifdef __x86_64__
    uint32_t a = 0, b = 0, c = 0, d = 0;
    __get_cpuid_count(1, 0, &a, &b, &c, &d);
    if (!(c & bit_OSXSAVE)) return &keccaktree_keccak256_generic;
    uint64_t xcr0 = xgetbv0();
    int os_ymm = (xcr0 & 0x6) == 0x6;
    int os_zmm = (xcr0 & 0xe6) == 0xe6;
    __get_cpuid_count(7, 0, &a, &b, &c, &d);
    if (os_zmm && (b & bit_AVX512F) && (b & bit_AVX512VL)) {
        return &keccaktree_keccak256_avx512_x8;
    }
    if (os_ymm && (b & bit_AVX2)) {
        return &keccaktree_keccak256_avx2_x4;
    }
#endif
#ifdef __aarch64__
#if defined(__APPLE__)
    return &keccaktree_keccak256_sha3_x2; /* every Apple M-series core has FEAT_SHA3 */
#elif defined(__linux__)
    unsigned long hwcaps = getauxval(AT_HWCAP);
#ifdef HWCAP_SHA3
    if (hwcaps & HWCAP_SHA3) return &keccaktree_keccak256_sha3_x2;
#endif
    if (hwcaps & HWCAP_ASIMD) return &keccaktree_keccak256_neon_x2;
#endif
#endif
    return &keccaktree_keccak256_generic;
}

void keccaktree_init(keccaktree_hash_fcn override) {
    hash_ptr = override ? override : keccaktree_detect();
}

void keccaktree_hash(unsigned char* output, const unsigned char* input, uint64_t count) {
    (*hash_ptr)(output, input, count);
}

static void init_and_hash(unsigned char* output, const unsigned char* input, uint64_t count) {
    hash_ptr = keccaktree_detect();
    keccaktree_hash(output, input, count);
}
