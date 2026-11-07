/* throwaway variant: avx512_x8 with the four-round loop body 64-byte aligned */
#define KT_LOOP_ALIGN 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8al
#include "keccak256_avx512_x8.S"
