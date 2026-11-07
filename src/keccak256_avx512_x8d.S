/* avx512_x8 with the D-form rounds (keccak256_avx512d.inc: all 25 lanes
 * in registers, 110 macro-ops per round), four-round loop body */
#define KT_DFORM 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8d
#include "keccak256_avx512_x8.S"
