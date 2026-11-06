/* Runtime dispatch, same contract as hashtree.c */
#include "keccaktree.h"

#ifdef __x86_64__
#include <cpuid.h>
#endif
#if defined(__aarch64__) && defined(__linux__)
#include <asm/hwcap.h>
#include <sys/auxv.h>
#endif
#if defined(__aarch64__) && defined(__APPLE__)
#include <sys/sysctl.h>
#endif

/* Kernel selection probes the instruction set extensions the kernel needs
 * (CPUID feature bits plus the OS register state from XGETBV on x86-64,
 * AT_HWCAP on Linux/AArch64, hw.optional sysctls on macOS), never CPU
 * vendors, families or models. Where several supported kernels fit, the
 * choice is a fixed default:
 *   AVX-512F+VL  avx512_x8  (avx512vl_x4 is the 1..4 node tail and an
 *                            override for cores with one 512-bit ALU port)
 *   AVX2         avx2_x8    (avx2_x4 via override)
 *   SHA3, Linux  sha3_x3    (lazy rotations; shifted-operand EOR/BIC at full
 *                            rate, as on Neoverse)
 *   SHA3, macOS  sha3_x3r   (explicit rotations: the arm64 macOS default,
 *                            as Apple's cores take 2 cycles per shifted operand)
 *   ASIMD        neon_x2    (scalar_x1 via override)
 * Every kernel stays callable directly or through keccaktree_init(). */

static void init_and_hash(unsigned char* output, const unsigned char* input, uint64_t count);
static keccaktree_hash_fcn hash_ptr = init_and_hash;

#if defined(__aarch64__) && defined(__APPLE__)
static int keccaktree_sysctl_flag(const char* name) {
    int v = 0;
    size_t len = sizeof(v);
    return sysctlbyname(name, &v, &len, NULL, 0) == 0 && v != 0;
}
#endif

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
        return &keccaktree_keccak256_avx2_x8;
    }
#endif
#ifdef __aarch64__
#if defined(__APPLE__)
    if (keccaktree_sysctl_flag("hw.optional.arm.FEAT_SHA3") || keccaktree_sysctl_flag("hw.optional.armv8_2_sha3"))
        return &keccaktree_keccak256_sha3_x3r;
    return &keccaktree_keccak256_neon_x2; /* Advanced SIMD is mandatory on AArch64 */
#elif defined(__linux__)
    unsigned long hwcaps = getauxval(AT_HWCAP);
#ifdef HWCAP_SHA3
    if (hwcaps & HWCAP_SHA3) return &keccaktree_keccak256_sha3_x3;
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
