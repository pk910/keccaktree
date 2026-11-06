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

/* Kernel selection probes the instruction set extensions a kernel needs
 * (CPUID feature bits plus the OS register state from XGETBV on x86-64,
 * AT_HWCAP on Linux/AArch64, hw.optional sysctls on macOS, riscv_hwprobe
 * and vlenb on Linux/RISC-V), never CPU
 * vendors, families or models.
 *
 * Some kernels differ only in how they suit the microarchitecture, a
 * property no feature bit reports: avx512vl_x4 beats avx512_x8 on cores
 * with a single 512-bit ALU port, sha3_x3 (lazy rotations) needs EOR/BIC
 * with a rotated operand at full rate, sha3_x3r does not, and scalar_x1
 * beats neon_x2 where the integer side outruns the vector side; on RISC-V
 * the scalar and vector kernels trade places with VLEN and the core. For these,
 * detection runs every feature-qualified candidate once on a small warm
 * batch and keeps the fastest (keccaktree_calibrate): tens of microseconds
 * up to ~0.5 ms, once per process. keccaktree_init(fn) skips it. */

#if defined(__riscv) && __riscv_xlen == 64
#ifdef __linux__
#include <sys/syscall.h>
#include <unistd.h>
#ifndef __NR_riscv_hwprobe
#define __NR_riscv_hwprobe 258 /* Linux 6.4+ */
#endif
#endif
/* riscv_hwprobe key and bits (asm/hwprobe.h, defined here for older headers) */
struct keccaktree_hwprobe { int64_t key; uint64_t value; };
#define KT_HWPROBE_KEY_IMA_EXT_0 4
#define KT_HWPROBE_IMA_V         (1ULL << 2)
#define KT_HWPROBE_EXT_ZBB       (1ULL << 4)
#define KT_HWPROBE_EXT_ZVKB      (1ULL << 19)
#endif

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

#if defined(__riscv) && __riscv_xlen == 64
static uint64_t keccaktree_riscv_vlenb(void) {
    uint64_t vlenb;
    __asm__ volatile(".option push\n.option arch, +v\ncsrr %0, vlenb\n.option pop" : "=r"(vlenb));
    return vlenb;
}
#endif

#if defined(__x86_64__) || defined(__aarch64__) || (defined(__riscv) && __riscv_xlen == 64)
/* Cheap monotonic tick counter, only compared against itself: the TSC on
 * x86-64, the generic timer's virtual count on AArch64 (readable from user
 * space on Linux and macOS), the time CSR on RISC-V (Zicntr, readable from
 * user space on Linux). */
static inline uint64_t keccaktree_ticks(void) {
#ifdef __x86_64__
    uint32_t lo, hi;
    __asm__ volatile("lfence\n\trdtsc" : "=a"(lo), "=d"(hi) : : "memory");
    return ((uint64_t)hi << 32) | lo;
#elif defined(__aarch64__)
    uint64_t t;
    __asm__ volatile("isb\n\tmrs %0, cntvct_el0" : "=r"(t) : : "memory");
    return t;
#else
    uint64_t t;
    __asm__ volatile(".option push\n.option arch, +zicsr\ncsrr %0, time\n.option pop" : "=r"(t) : : "memory");
    return t;
#endif
}

/* A multiple of every kernel's batch (2, 3, 4, 8). Each sample hashes the
 * buffer in place twice (96 nodes, long enough for the 24 MHz counter of
 * Apple cores to resolve a few percent; keccak's timing does not depend on
 * the data); one 3 KB buffer keeps the frame below the 4 KB at which
 * Windows compilers emit a stack probe call. */
#define CALIB_NODES 48
#define CALIB_REPS  7

/* Times each candidate, interleaved so a frequency change hits all of them
 * alike, and returns the one with the lowest minimum. */
static keccaktree_hash_fcn keccaktree_calibrate(const keccaktree_hash_fcn* fns, int n) {
    unsigned char buf[CALIB_NODES * 64] __attribute__((aligned(64)));
    uint64_t best[4];
    for (int i = 0; i < CALIB_NODES * 64; i++) buf[i] = (unsigned char)(i * 131 + 7);
    for (int i = 0; i < n; i++) {
        fns[i](buf, buf, CALIB_NODES); /* warm code, data and vector units */
        best[i] = UINT64_MAX;
    }
    for (int r = 0; r < CALIB_REPS; r++) {
        for (int i = 0; i < n; i++) {
            uint64_t t0 = keccaktree_ticks();
            fns[i](buf, buf, CALIB_NODES);
            fns[i](buf, buf, CALIB_NODES);
            uint64_t t = keccaktree_ticks() - t0;
            if (t < best[i]) best[i] = t;
        }
    }
    int pick = 0;
    for (int i = 1; i < n; i++)
        if (best[i] < best[pick]) pick = i;
    return fns[pick];
}
#endif

keccaktree_hash_fcn keccaktree_detect(void) {
#ifdef __x86_64__
    uint32_t a = 0, b = 0, c = 0, d = 0;
    __get_cpuid_count(1, 0, &a, &b, &c, &d);
    if (!(c & bit_OSXSAVE)) return &keccaktree_keccak256_generic;
    uint64_t xcr0 = xgetbv0();
    int os_ymm = (xcr0 & 0x6) == 0x6;
    int os_zmm = (xcr0 & 0xe6) == 0xe6;
    __get_cpuid_count(7, 0, &a, &b, &c, &d);
    if (os_zmm && (b & bit_AVX512F) && (b & bit_AVX512VL)) {
        static const keccaktree_hash_fcn c[] = {&keccaktree_keccak256_avx512_x8,
                                                &keccaktree_keccak256_avx512vl_x4};
        return keccaktree_calibrate(c, 2);
    }
    /* the AVX2 kernels hand single nodes to x86_x1, which needs BMI1 and
     * BMI2 (every AVX2 core has them; a hypervisor could hide them) */
    int bmi = (b & bit_BMI) && (b & bit_BMI2);
    if (os_ymm && (b & bit_AVX2) && bmi) {
        static const keccaktree_hash_fcn c[] = {&keccaktree_keccak256_avx2_x8,
                                                &keccaktree_keccak256_avx2_x4};
        return keccaktree_calibrate(c, 2);
    }
    if (bmi) return &keccaktree_keccak256_x86_x1;
#endif
#ifdef __aarch64__
    static const keccaktree_hash_fcn sha3[] = {&keccaktree_keccak256_sha3_x3,
                                               &keccaktree_keccak256_sha3_x3r,
                                               &keccaktree_keccak256_sha3_x2};
    static const keccaktree_hash_fcn simd[] = {&keccaktree_keccak256_neon_x2,
                                               &keccaktree_keccak256_scalar_x1};
#if defined(__APPLE__)
    if (keccaktree_sysctl_flag("hw.optional.arm.FEAT_SHA3") || keccaktree_sysctl_flag("hw.optional.armv8_2_sha3"))
        return keccaktree_calibrate(sha3, 3);
    return keccaktree_calibrate(simd, 2); /* Advanced SIMD is mandatory on AArch64 */
#elif defined(__linux__)
    unsigned long hwcaps = getauxval(AT_HWCAP);
#ifdef HWCAP_SHA3
    if (hwcaps & HWCAP_SHA3) return keccaktree_calibrate(sha3, 3);
#endif
    if (hwcaps & HWCAP_ASIMD) return keccaktree_calibrate(simd, 2);
#endif
#endif
#if defined(__riscv) && __riscv_xlen == 64
    uint64_t ext = 0;
#ifdef __linux__
    struct keccaktree_hwprobe probe = {KT_HWPROBE_KEY_IMA_EXT_0, 0};
    if (syscall(__NR_riscv_hwprobe, &probe, 1, 0, NULL, 0) == 0 && probe.key == KT_HWPROBE_KEY_IMA_EXT_0)
        ext = probe.value;
#endif
    /* V in IMA_EXT_0 means the kernel has enabled it, so vlenb is readable;
     * the vector kernels need VLEN >= 128 (2 nodes per register) */
    int v = (ext & KT_HWPROBE_IMA_V) && keccaktree_riscv_vlenb() >= 16;
    keccaktree_hash_fcn c[4];
    int n = 0;
    c[n++] = &keccaktree_keccak256_rv64_x1;
    if (ext & KT_HWPROBE_EXT_ZBB) c[n++] = &keccaktree_keccak256_zbb_x1;
    if (v) c[n++] = &keccaktree_keccak256_rvv;
    if (v && (ext & KT_HWPROBE_EXT_ZVKB)) c[n++] = &keccaktree_keccak256_rvv_zvkb;
    return keccaktree_calibrate(c, n);
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
