/* throwaway variant: avx512_x9 with one scalar chunk per vector hook (55 of
 * the 65 chunks spread, 10 flushed at the end of the round) */
#define NS 1
#define SNUM 1
#define SDEN 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x9b
#include "keccak256_avx512_x8.S"
