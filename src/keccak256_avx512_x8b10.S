/* throwaway variant: avx512_x8 with both copied chi outputs of every row as
 * vpandnq + vpxorq (CHI_ANDN 2: +10 ALU ops, -10 copies per round) */
#define CHI_ANDN 2
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8b10
#include "keccak256_avx512_x8.S"
