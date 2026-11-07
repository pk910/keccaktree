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

/** Select the implementation, or auto-detect from the CPU when `NULL`:
 * probe the CPU features, then time the kernels the CPU supports once on a
 * small batch and keep the fastest (well under a millisecond).
 * Optional: auto-detection also happens on the first hash call. */
void keccaktree_init(keccaktree_hash_fcn override);

/** The kernel auto-detection picks (feature probe plus the one-time timing
 * of the supported kernels), without installing it. Each call measures
 * again; keccaktree_init(NULL) caches the result. */
keccaktree_hash_fcn keccaktree_detect(void);

void keccaktree_hash(unsigned char* output, const unsigned char* input, uint64_t count);

/* Portable C, one node at a time. Works on every platform and endianness. */
void keccaktree_keccak256_generic(unsigned char* output, const unsigned char* input, uint64_t count);

#ifdef __x86_64__
/* Undefined behavior if called without appropriate hardware support */
void keccaktree_keccak256_avx2_x4(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x8(unsigned char* output, const unsigned char* input, uint64_t count);
/* 2 nodes at a time (lane pairs); avx2_x4 hands 2 remaining nodes to it
 * once keccaktree_avx2_small_tail(2) enables that (keccaktree_detect does
 * where it beats a padded batch; 1 restores the padded batch) */
void keccaktree_keccak256_avx2_x2(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_avx2_small_tail(uint64_t max);
/* avx2_x8 interleaved with one or two nodes in the general registers, and
 * avx2_x4 with one or two (AVX2 + BMI1 + BMI2) */
void keccaktree_keccak256_avx2_x9(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x10(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x5(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x6(unsigned char* output, const unsigned char* input, uint64_t count);
/* after an avx2_x10 batch, 5..max remaining nodes go to avx2_x5 (max = 9,
 * or 5: just five; the default is 4, a padded x10 batch for all;
 * keccaktree_detect times 5 and 9) */
void keccaktree_avx2_x10_mid_tail(uint64_t max);
void keccaktree_keccak256_avx512vl_x4(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x8(unsigned char* output, const unsigned char* input, uint64_t count);
/* avx512_x8 interleaved with one node in the general registers (AVX-512F
 * + VL + BMI1 + BMI2): cores whose 512-bit units leave the integer side
 * and the dispatch width idle (Zen 4) */
void keccaktree_keccak256_avx512_x9(unsigned char* output, const unsigned char* input, uint64_t count);
/* the same three with the D-form rounds (all 25 lanes in registers, 35
 * instead of 60 vpternlogq per round): faster on AMD (Zen 4 avx512_x9d
 * 1.17x avx512_x9, Zen 5 avx512_x8d 1.19x avx512_x8), slower on Ice Lake;
 * keccaktree_detect times them against the others */
void keccaktree_keccak256_avx512vl_x4d(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x8d(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x9d(unsigned char* output, const unsigned char* input, uint64_t count);
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
