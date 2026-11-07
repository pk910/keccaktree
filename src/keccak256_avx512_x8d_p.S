/* throwaway D-form variant p (see gen_avx512d.py options) */
#define KT_DFORM 1
#define KT_DFORM_FILE "keccak256_avx512d_p.inc"
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8d_p
#include "keccak256_avx512_x8.S"
