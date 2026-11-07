/* throwaway variant: avx512_x9 with 3 scalar chunks per 2 vector hooks (the
 * scalar round is complete after hook 44 of 55) */
#define NS 1
#define SNUM 3
#define SDEN 2
#define KERNEL_NAME	keccaktree_keccak256_avx512_x9c
#include "keccak256_avx512_x8.S"
