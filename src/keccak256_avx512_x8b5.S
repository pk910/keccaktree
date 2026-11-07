/* throwaway variant: avx512_x8 with the first chi output of every row as
 * vpandnq + vpxorq instead of copy + vpternlogq (CHI_ANDN 1: +5 ALU ops,
 * -5 copies per round) */
#define CHI_ANDN 1
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8b5
#include "keccak256_avx512_x8.S"
