/*
 * void keccaktree_keccak256_avx512_x9d(unsigned char *output,
 *                                      const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 9 at a time:
 * keccak256_avx512_x9.S (the 8-node zmm batch plus one node in the general
 * registers, keccak256_x86_scalar.inc) with the D-form rounds of
 * keccak256_avx512d.inc. The pick on Zen 4 (EPYC 9V74: 43.4 ns/node,
 * 1.166x avx512_x9, 1.24x avx512_x8; the scalar node costs 1.3 of the
 * round's 60 cycles); on Zen 5 avx512_x8d is faster, on Intel the integer
 * ALUs share the vector ports and avx512_x8 / avx512_x8d win.
 * Needs AVX-512F + VL, BMI1 and BMI2; keccaktree_detect times it.
 *
 * Remaining nodes: 1 to keccaktree_keccak256_x86_x1, 2..4 to
 * keccaktree_keccak256_avx512vl_x4d, 5..8 a padded batch here; whole calls
 * of 8, 16, ... 56 nodes go to avx512_x8d.
 */
#define KT_DFORM 1
#define NS 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x9d
#define SMALL_TAIL	keccaktree_keccak256_avx512vl_x4d
#define ENTRY_ALT	keccaktree_keccak256_avx512_x8d
#include "keccak256_avx512_x8.S"
