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

/* Kernel selection reads what the CPU reports about itself and nothing
 * else: no kernel is run or timed to choose one, so the first hash call
 * costs a handful of CPUID reads (x86-64), one getauxval and one emulated
 * MIDR_EL1 read (Linux/AArch64), two sysctls (macOS) or one riscv_hwprobe
 * call (Linux/RISC-V), and every process on a machine picks the same
 * kernel whatever core it happens to start on.
 *
 * The instruction set extensions decide what can run (CPUID feature bits
 * plus the OS register state from XGETBV, AT_HWCAP, hw.optional,
 * riscv_hwprobe and vlenb). Where several kernels can run and differ only
 * in how they suit the core, a short table of the cores they were measured
 * on decides (vendor, family, core type, MIDR implementer and part); an
 * unknown core gets the kernel with the smallest loss on the measured
 * ones. The Go bindings apply the same rules to the same inputs
 * (bindings_*.go); a change here needs the same change there.
 *
 * An earlier version timed the candidates once per process instead. That
 * took 0.25 to 0.5 ms at the first call, and on CPUs with two kinds of
 * cores it measured whichever core the first call ran on: on a Core
 * i9-14900K 87% of the processes started on an E-core and kept avx2_x6
 * for good, which runs 54% slower than avx2_x8 on the P-cores. */

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

#ifdef __x86_64__
/* x86-64. Every assembly kernel needs BMI1 and BMI2 (the scalar kernel
 * x86_x1 and the scalar nodes of the hybrids use andn and rorx, and every
 * vector kernel hands its last node to x86_x1); a hypervisor can hide them
 * from a CPU that has AVX2, and then the portable C runs.
 *
 * AVX-512 (F + VL + BW: the rotations by 8 and 56 are EVEX vpshufb; zmm
 * state enabled), ns per node at 1024 nodes relative
 * to avx512_x8:
 *   AMD family 19h (Zen 4)          avx512_x9d    1.24x: the double-pumped
 *                                   512-bit units leave the integer ALUs
 *                                   and the dispatch width to a scalar node
 *   Intel Cannon/Ice/Tiger/Rocket   avx512vl_x4   one 512-bit ALU port, but
 *   Lake client                                   three for 256-bit ops
 *   Intel without AVX512-FP16       avx512_x8     Ice Lake server: x8d
 *   (Skylake-SP .. Ice Lake)                      0.935x, two 512-bit ports
 *                                                 that count ALU ops
 *   everything else (Zen 5: 1.19x,  avx512_x8d    35 instead of 60
 *   Emerald Rapids 1.035x, Granite                vpternlogq per round
 *   Rapids 1.006x)
 * avx512_x9d is 0.87x avx512_x8d on Zen 5 and 0.6..0.9x on Intel, so it is
 * only picked where it was measured to win.
 *
 * AVX2, ns per node at 1024 nodes (best kernel first):
 *   Zen 3            x10 67, x5 ~75, x8 81
 *   Raptor Cove (P)  x8 69, x4 71, x5 77, x10 83, x6 106
 *   Gracemont (E)    x6 136, x5 137, x10 142, x4 178, x8 179
 * so: AMD and Hygon avx2_x10; Intel avx2_x8, or avx2_x6 where CPUID leaf
 * 1AH reports an Atom core (Alder Lake-N, Sierra Forest); CPUs with both
 * kinds of cores the per-core dispatcher avx2_hybrid, which picks between
 * those two on every call; any other vendor avx2_x5, at most 12% behind
 * the best kernel on each of the three. */
static void keccaktree_cpuid(uint32_t leaf, uint32_t sub, uint32_t r[4]) {
    r[0] = r[1] = r[2] = r[3] = 0;
    __get_cpuid_count(leaf, sub, &r[0], &r[1], &r[2], &r[3]);
}

keccaktree_hash_fcn keccaktree_detect(void) {
    uint32_t r[4];
    keccaktree_cpuid(0, 0, r);
    uint32_t max_leaf = r[0];
    int intel = r[1] == 0x756e6547 && r[3] == 0x49656e69 && r[2] == 0x6c65746e; /* GenuineIntel */
    int amd = (r[1] == 0x68747541 && r[3] == 0x69746e65 && r[2] == 0x444d4163) || /* AuthenticAMD */
              (r[1] == 0x6f677948 && r[3] == 0x6e65476e && r[2] == 0x656e6975);   /* HygonGenuine */
    keccaktree_cpuid(1, 0, r);
    if (max_leaf < 7 || !(r[2] & bit_OSXSAVE)) return &keccaktree_keccak256_generic;
    uint32_t family = (r[0] >> 8) & 0xf, model = (r[0] >> 4) & 0xf;
    if (family == 0xf) family += (r[0] >> 20) & 0xff;
    if (family >= 6) model |= ((r[0] >> 16) & 0xf) << 4;
    uint64_t xcr0 = xgetbv0();
    int os_ymm = (xcr0 & 0x6) == 0x6;
    int os_zmm = (xcr0 & 0xe6) == 0xe6;
    keccaktree_cpuid(7, 0, r);
    if (!(r[1] & bit_BMI) || !(r[1] & bit_BMI2)) return &keccaktree_keccak256_generic;
    if (os_zmm && (r[1] & bit_AVX512F) && (r[1] & bit_AVX512VL) && (r[1] & bit_AVX512BW)) {
        if (amd && family == 0x19) return &keccaktree_keccak256_avx512_x9d;
        if (intel && family == 6 &&
            (model == 0x66 || model == 0x7d || model == 0x7e || model == 0x8c || model == 0x8d || model == 0xa7))
            return &keccaktree_keccak256_avx512vl_x4;
        if (intel && !(r[3] & (1u << 23))) return &keccaktree_keccak256_avx512_x8; /* no AVX512-FP16 */
        return &keccaktree_keccak256_avx512_x8d;
    }
    if (os_ymm && (r[1] & bit_AVX2)) {
        int hybrid = (r[3] >> 15) & 1, rdpid = (r[2] >> 22) & 1;
        if (hybrid && rdpid && max_leaf >= 0x1a) return &keccaktree_keccak256_avx2_hybrid;
        if (amd) return &keccaktree_keccak256_avx2_x10;
        if (intel && !hybrid) {
            if (max_leaf >= 0x1a) {
                keccaktree_cpuid(0x1a, 0, r);
                if ((r[0] >> 24) == 0x20) return &keccaktree_keccak256_avx2_x6;
            }
            return &keccaktree_keccak256_avx2_x8;
        }
        return &keccaktree_keccak256_avx2_x5;
    }
    return &keccaktree_keccak256_x86_x1;
}
#elif defined(__aarch64__)
/* AArch64. Advanced SIMD is part of the base architecture; FEAT_SHA3
 * (EOR3, RAX1, XAR, BCAX) selects the sha3 kernels. Which of them, and
 * which kernel without FEAT_SHA3, depends on how the core runs an EOR/BIC
 * with a rotated operand, which the lazy-rotation scalar node of sha3_x3,
 * neon_x3 and scalar_x1 relies on:
 *   Arm Ltd cores with FEAT_SHA3    sha3_x3    full rate (Neoverse N2: 122
 *   (MIDR implementer 41H)                     ns per node, sha3_x2 178)
 *   Apple cores (61H, and macOS)    sha3_x3r   a rotated operand costs
 *                                              extra: explicit rotations
 *                                              (M1: 66, sha3_x2 77)
 *   other cores with FEAT_SHA3      sha3_x2
 *   Neoverse N1 and Cortex-A76      neon_x3    233 against 276 (scalar_x1)
 *   (the same core; 41H, parts                 and 340 (neon_x2) on N1
 *   D0CH and D0BH)
 *   everything else                 neon_x2    older cores (A72, A57) run
 *                                              the rotated form on one pipe
 * Linux emulates MIDR_EL1 reads from user space when it reports
 * HWCAP_CPUID; without it the implementer is unknown. */
keccaktree_hash_fcn keccaktree_detect(void) {
#if defined(__APPLE__)
    if (keccaktree_sysctl_flag("hw.optional.arm.FEAT_SHA3") || keccaktree_sysctl_flag("hw.optional.armv8_2_sha3"))
        return &keccaktree_keccak256_sha3_x3r;
    return &keccaktree_keccak256_neon_x2;
#elif defined(__linux__)
    unsigned long hwcaps = getauxval(AT_HWCAP);
    unsigned implementer = 0, part = 0;
#ifdef HWCAP_CPUID
    if (hwcaps & HWCAP_CPUID) {
        uint64_t midr;
        __asm__("mrs %0, MIDR_EL1" : "=r"(midr));
        implementer = (unsigned)(midr >> 24) & 0xff;
        part = (unsigned)(midr >> 4) & 0xfff;
    }
#endif
#ifdef HWCAP_SHA3
    if (hwcaps & HWCAP_SHA3)
        return implementer == 0x41   ? &keccaktree_keccak256_sha3_x3
               : implementer == 0x61 ? &keccaktree_keccak256_sha3_x3r
                                     : &keccaktree_keccak256_sha3_x2;
#endif
    if (implementer == 0x41 && (part == 0xd0c || part == 0xd0b)) return &keccaktree_keccak256_neon_x3;
    return &keccaktree_keccak256_neon_x2;
#else
    return &keccaktree_keccak256_generic;
#endif
}
#elif defined(__riscv) && __riscv_xlen == 64
/* RISC-V. Not measured on hardware, chosen by instruction counts: per
 * batch and round rvv_zvkb issues 131 vector instructions and rvv 214,
 * while one node costs zbb_x1 145 and rv64_x1 228 scalar ones. With Zvkb
 * the vector kernel wins at any VLEN; without it only from VLEN = 256 (4
 * nodes per batch) on, as at VLEN = 128 its 107 instructions per node are
 * no better than a dual-issue scalar core running zbb_x1. */
static keccaktree_hash_fcn keccaktree_riscv_select(uint64_t ext, uint64_t vlenb) {
    int v = (ext & KT_HWPROBE_IMA_V) && vlenb >= 16;
    if (v && (ext & KT_HWPROBE_EXT_ZVKB)) return &keccaktree_keccak256_rvv_zvkb;
    if (v && vlenb >= 32) return &keccaktree_keccak256_rvv;
    if (ext & KT_HWPROBE_EXT_ZBB) return &keccaktree_keccak256_zbb_x1;
    if (v) return &keccaktree_keccak256_rvv;
    return &keccaktree_keccak256_rv64_x1;
}

keccaktree_hash_fcn keccaktree_detect(void) {
    uint64_t ext = 0;
#ifdef __linux__
    struct keccaktree_hwprobe probe = {KT_HWPROBE_KEY_IMA_EXT_0, 0};
    if (syscall(__NR_riscv_hwprobe, &probe, 1, 0, NULL, 0) == 0 && probe.key == KT_HWPROBE_KEY_IMA_EXT_0)
        ext = probe.value;
#endif
    /* V in IMA_EXT_0 means the kernel has enabled it, so vlenb is readable */
    return keccaktree_riscv_select(ext, (ext & KT_HWPROBE_IMA_V) ? keccaktree_riscv_vlenb() : 0);
}
#else
keccaktree_hash_fcn keccaktree_detect(void) {
    return &keccaktree_keccak256_generic;
}
#endif

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
