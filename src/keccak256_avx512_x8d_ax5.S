/* throwaway D-form variant ax5 (see gen_avx512d.py options) */
#define KT_DFORM 1
#define KT_DFORM_FILE "keccak256_avx512d_ax5.inc"
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8d_ax5
#include "keccak256_avx512_x8.S"
