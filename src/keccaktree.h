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

void keccaktree_hash(unsigned char* output, const unsigned char* input, uint64_t count);

/* Portable C, one node at a time. Works on every platform and endianness. */
void keccaktree_keccak256_generic(unsigned char* output, const unsigned char* input, uint64_t count);

#ifdef __x86_64__
/* Undefined behavior if called without appropriate hardware support */
void keccaktree_keccak256_avx2_x4(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512vl_x4(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_avx512_x8(unsigned char* output, const unsigned char* input, uint64_t count);
/* 1 on Intel client cores whose 512-bit integer ops issue on one port only;
 * keccaktree_hash then uses avx512vl_x4 instead of avx512_x8 */
int keccaktree_avx512_single_port(void);
#endif

#ifdef __aarch64__
void keccaktree_keccak256_neon_x2(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_sha3_x2(unsigned char* output, const unsigned char* input, uint64_t count);
/* lazy-rotation scalar, and sha3_x2 interleaved with it (Arm Ltd cores) */
void keccaktree_keccak256_scalar_x1(unsigned char* output, const unsigned char* input, uint64_t count);
void keccaktree_keccak256_sha3_x3(unsigned char* output, const unsigned char* input, uint64_t count);
/* sha3_x2 interleaved with a plain-rotation scalar node (Apple cores) */
void keccaktree_keccak256_sha3_x3r(unsigned char* output, const unsigned char* input, uint64_t count);

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
