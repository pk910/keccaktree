/*
 * void keccaktree_keccak256_avx512_x9(unsigned char *output,
 *                                     const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 9 at a time: the
 * 8-node zmm batch of keccak256_avx512_x8.S plus one node in the general
 * registers (keccak256_x86_scalar.inc), the scalar round's instructions
 * spread through the vector round. For cores that run 512-bit operations
 * at half rate on their vector pipes (Zen 4: the 90 vector ALU operations
 * of a round take about 45 cycles, during which the front end dispatches
 * under two instructions per cycle and the integer ALUs idle); on Ice
 * Lake the integer ALUs share ports 0 and 5 with the vector units and
 * this kernel loses. Needs AVX-512F + VL, BMI1 and BMI2;
 * keccaktree_detect times it against avx512_x8.
 *
 * Remaining nodes: 1 to keccaktree_keccak256_x86_x1, 2..4 to
 * keccaktree_keccak256_avx512vl_x4, 5..8 a padded batch here; whole calls
 * of 8, 16, ... 56 nodes go to avx512_x8.
 */
#define NS 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x9
#include "keccak256_avx512_x8.S"
