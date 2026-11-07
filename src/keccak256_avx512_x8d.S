/*
 * void keccaktree_keccak256_avx512_x8d(unsigned char *output,
 *                                      const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 8 at a time:
 * keccak256_avx512_x8.S (frame, transposes, tails) with the D-form rounds
 * of keccak256_avx512d.inc, which keep all 25 lanes in registers and use
 * 35 instead of 60 vpternlogq per round. Faster on AMD (Zen 4: 1.12x
 * avx512_x8, Zen 5: 1.19x) and on Emerald / Granite Rapids, slower on
 * Ice Lake (0.935x, two 512-bit ALU ports); keccaktree_detect times both.
 * AVX-512F + VL, BMI1 + BMI2 for the single-node tail. 2..4 remaining
 * nodes go to keccaktree_keccak256_avx512vl_x4d.
 */
#define KT_DFORM 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8d
#define SMALL_TAIL	keccaktree_keccak256_avx512vl_x4d
#include "keccak256_avx512_x8.S"
