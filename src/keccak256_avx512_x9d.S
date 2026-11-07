/* avx512_x9 (one scalar node interleaved) with the D-form rounds */
#define KT_DFORM 1
#define NS 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x9d
#include "keccak256_avx512_x8.S"
