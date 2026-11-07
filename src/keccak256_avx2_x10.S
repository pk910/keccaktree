/*
 * void keccaktree_keccak256_avx2_x10(unsigned char *output,
 *                                    const unsigned char *input, uint64_t count)
 *
 * keccak256_avx2_x9 with two scalar nodes: the round of one runs during
 * the vector round of batch A, the round of the other during batch B's.
 */
#define NS 2
#include "keccak256_avx2_x9.S"
