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

/* Intel client cores with AVX-512 (Cannon/Ice/Tiger/Rocket Lake) execute
 * 512-bit integer ops on a single port (p0+p1 fused, no 512-bit ALU on p5),
 * while 256-bit ops still use three. There the 4-lane ymm kernel moves 12
 * lanes per cycle against 8 for the zmm kernel. Server parts (Skylake-SP and
 * later) and AMD Zen 4/5 have two 512-bit pipes and keep the zmm kernel. */
int keccaktree_avx512_single_port(void) {
    uint32_t a = 0, b = 0, c = 0, d = 0;
    __get_cpuid(0, &a, &b, &c, &d);
    if (b != 0x756e6547 || d != 0x49656e69 || c != 0x6c65746e) return 0; /* GenuineIntel */
    __get_cpuid(1, &a, &b, &c, &d);
    unsigned family = (a >> 8) & 0xf, model = ((a >> 4) & 0xf) | (((a >> 16) & 0xf) << 4);
    if (family != 6) return 0;
    switch (model) {
    case 0x66:             /* Cannon Lake */
    case 0x7d: case 0x7e:  /* Ice Lake client */
    case 0x8c: case 0x8d:  /* Tiger Lake */
    case 0xa7:             /* Rocket Lake */
        return 1;
    }
    return 0;
}
#endif

#if defined(__aarch64__) && defined(__linux__)
/* The lazy-rotation kernels (scalar_x1, sha3_x3) rely on EOR/BIC with a
 * rotated operand being as cheap as a plain one: true on Arm Ltd cores
 * (implementer 0x41: Neoverse, Cortex-A7xx/X), false on Apple's. Without
 * FEAT_SHA3 the scalar kernel is only picked on Neoverse N1 (Graviton 2,
 * Ampere Altra), whose integer pipes take the rotated form at full rate;
 * older Cortex-A cores (A72, A57) run it on one pipe and keep neon_x2.
 * Apple cores (implementer 0x61, also under Linux) get sha3_x3r, the
 * hybrid with explicit rotations. */
static void keccaktree_arm_select(unsigned implementer, unsigned part, int* arm_core, int* n1, int* apple) {
    *arm_core = implementer == 0x41;
    *n1 = implementer == 0x41 && part == 0xd0c;
    *apple = implementer == 0x61;
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
        return keccaktree_avx512_single_port() ? &keccaktree_keccak256_avx512vl_x4
                                               : &keccaktree_keccak256_avx512_x8;
    }
    if (os_ymm && (b & bit_AVX2)) {
        return &keccaktree_keccak256_avx2_x8;
    }
#endif
#ifdef __aarch64__
#if defined(__APPLE__)
    return &keccaktree_keccak256_sha3_x3r; /* every Apple M-series core has FEAT_SHA3 */
#elif defined(__linux__)
    unsigned long hwcaps = getauxval(AT_HWCAP);
    int arm_core = 0, n1 = 0, apple = 0;
#ifdef HWCAP_CPUID
    if (hwcaps & HWCAP_CPUID) { /* the kernel emulates MIDR_EL1 reads */
        uint64_t midr;
        __asm__("mrs %0, MIDR_EL1" : "=r"(midr));
        keccaktree_arm_select((unsigned)(midr >> 24) & 0xff, (unsigned)(midr >> 4) & 0xfff, &arm_core, &n1, &apple);
    }
#endif
#ifdef HWCAP_SHA3
    if (hwcaps & HWCAP_SHA3)
        return arm_core ? &keccaktree_keccak256_sha3_x3
             : apple    ? &keccaktree_keccak256_sha3_x3r
                        : &keccaktree_keccak256_sha3_x2;
#endif
    if (n1) return &keccaktree_keccak256_scalar_x1;
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
