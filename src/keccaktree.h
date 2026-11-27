/*
MIT License

Keccaktree: batched keccak256 for Merkle trees, API-compatible with hashtree.
*/
#ifndef KECCAKTREE_H
#define KECCAKTREE_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Same shape as hashtree_hash_fcn: hash `count` 64-byte chunks from `input`
 * into `count` consecutive 32-byte digests in `output`.
 * digest[i] = keccak256(input[64*i .. 64*i+63])   (Ethereum keccak256, pad 0x01)
 * `output` may alias `input` (in-place layer reduction, output == input). */
typedef void (*keccaktree_hash_fcn)(unsigned char*, const unsigned char*, uint64_t);

/** Select the implementation, or auto-detect from the CPU when `NULL`.
 * Optional: auto-detection also happens on the first hash call. */
void keccaktree_init(keccaktree_hash_fcn override);

/** The kernel auto-detection picks, without installing it. It only reads
 * what the CPU reports (feature bits, vendor, family, core type: a few
 * CPUID reads or one getauxval / sysctl / riscv_hwprobe call); nothing is
 * run or timed, so it is cheap and returns the same kernel on every call
 * and in every process on a machine. */
keccaktree_hash_fcn keccaktree_detect(void);

void keccaktree_hash(unsigned char* output, const unsigned char* input, uint64_t count);

/* Portable C, one node at a time. Works on every platform and endianness. */
void keccaktree_keccak256_generic(unsigned char* output, const unsigned char* input, uint64_t count);

#ifdef __x86_64__
/* Undefined behavior if called without appropriate hardware support */
void keccaktree_keccak256_avx2_x4(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x8(unsigned char* output, const unsigned char* input, uint64_t count);
/* 2 nodes at a time (lane pairs); avx2_x10 hands calls of 2 nodes to it */
void keccaktree_keccak256_avx2_x2(unsigned char* output, const unsigned char* input, uint64_t count);
/* avx2_x8 interleaved with one or two nodes in the general registers, and
 * avx2_x4 with one or two (AVX2 + BMI1 + BMI2) */
void keccaktree_keccak256_avx2_x9(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x10(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x5(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x6(unsigned char* output, const unsigned char* input, uint64_t count);
/* the AVX-512 kernels need AVX-512F, VL and BW, and BMI1 + BMI2 */
void keccaktree_keccak256_avx512vl_x4(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x8(unsigned char* output, const unsigned char* input, uint64_t count);
/* avx512_x8 interleaved with one node in the general registers (AVX-512F
 * + VL + BW + BMI1 + BMI2): cores whose 512-bit units leave the integer side
 * and the dispatch width idle (Zen 4) */
void keccaktree_keccak256_avx512_x9(unsigned char* output, const unsigned char* input, uint64_t count);
/* the same three with the D-form rounds (all 25 lanes in registers, 35
 * instead of 60 vpternlogq per round): faster on AMD (Zen 4 avx512_x9d
 * 1.17x avx512_x9, Zen 5 avx512_x8d 1.19x avx512_x8), slower on Ice Lake;
 * keccaktree_detect picks them by vendor, family and AVX512-FP16 */
void keccaktree_keccak256_avx512vl_x4d(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x8d(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x9d(unsigned char* output, const unsigned char* input, uint64_t count);
/* per-core dispatch for CPUs with two kinds of cores (CPUID hybrid flag;
 * needs RDPID): avx2_x8 on the P-cores, avx2_x6 on the E-cores, looked up
 * on every call from the logical CPU the call runs on */
void keccaktree_keccak256_avx2_hybrid(unsigned char* output, const unsigned char* input, uint64_t count);
/* one node at a time in the general registers (BMI1 + BMI2); the AVX2
 * kernels hand their single remaining node to it */
void keccaktree_keccak256_x86_x1(unsigned char* output, const unsigned char* input, uint64_t count);
#endif

#ifdef __aarch64__
void keccaktree_keccak256_neon_x2(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_sha3_x2(unsigned char* output, const unsigned char* input, uint64_t count);
/* lazy-rotation scalar, and sha3_x2 interleaved with it (cores that run a
 * shifted-operand EOR/BIC at full rate) */
void keccaktree_keccak256_scalar_x1(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_sha3_x3(unsigned char* output, const unsigned char* input, uint64_t count);
/* neon_x2 interleaved with the lazy-rotation scalar node (cores without
 * FEAT_SHA3 whose integer side has room beside the vector side) */
void keccaktree_keccak256_neon_x3(unsigned char* output, const unsigned char* input, uint64_t count);
/* sha3_x2 interleaved with a plain-rotation scalar node (cores where a
 * shifted operand costs extra) */
void keccaktree_keccak256_sha3_x3r(unsigned char* output, const unsigned char* input, uint64_t count);

#endif

#if defined(__riscv) && __riscv_xlen == 64
/* one node at a time in the general registers: base RV64I, and with Zbb */
void keccaktree_keccak256_rv64_x1(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_zbb_x1(unsigned char* output, const unsigned char* input, uint64_t count);
/* VLEN/64 nodes at a time with RVV 1.0, and with RVV 1.0 + Zvkb */
void keccaktree_keccak256_rvv(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_rvv_zvkb(unsigned char* output, const unsigned char* input, uint64_t count);
#endif

#ifdef KECCAKTREE_HASHTREE_COMPAT
/* Source-level drop-in: code written against hashtree.h compiles unchanged. */
#define hashtree_hash_fcn keccaktree_hash_fcn
#define hashtree_init keccaktree_init
#define hashtree_hash keccaktree_hash
#endif

#ifdef __cplusplus
}
#endif
#endif
