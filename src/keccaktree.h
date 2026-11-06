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
/* avx2_x8 interleaved with one or two nodes in the general registers (AVX2 + BMI1 + BMI2) */
void keccaktree_keccak256_avx2_x9(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx2_x10(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512vl_x4(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x8(unsigned char* output, const unsigned char* input, uint64_t count);
#endif

#ifdef __aarch64__
void keccaktree_keccak256_neon_x2(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_sha3_x2(unsigned char* output, const unsigned char* input, uint64_t count);
/* lazy-rotation scalar, and sha3_x2 interleaved with it (cores that run a
 * shifted-operand EOR/BIC at full rate) */
void keccaktree_keccak256_scalar_x1(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_sha3_x3(unsigned char* output, const unsigned char* input, uint64_t count);
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
