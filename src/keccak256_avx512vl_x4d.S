/*
 * void keccaktree_keccak256_avx512vl_x4d(unsigned char *output,
 *                                        const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 4 at a time on ymm
 * registers: keccak256_avx512vl_x4.S with the D-form rounds of
 * keccak256_avx512d.inc (Zen 4: 1.18x avx512vl_x4, Zen 5: 1.17x, Ice
 * Lake: 0.94x). The 2..4-node tail of avx512_x8d and avx512_x9d.
 * AVX-512F + VL, BMI1 + BMI2 for the single-node tail.
 */
#define KT_DFORM 1
#define KERNEL_NAME	keccaktree_keccak256_avx512vl_x4d
#include "keccak256_avx512vl_x4.S"
