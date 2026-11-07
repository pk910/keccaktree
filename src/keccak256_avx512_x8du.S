/* avx512_x8 with the D-form rounds, fully unrolled */
#define KT_DFORM 1
#define KT_AVX512_UNROLLED 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8du
#include "keccak256_avx512_x8.S"
