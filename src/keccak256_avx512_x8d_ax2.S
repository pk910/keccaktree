/* throwaway D-form variant ax2 (see gen_avx512d.py options) */
#define KT_DFORM 1
#define KT_DFORM_FILE "keccak256_avx512d_ax2.inc"
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8d_ax2
#include "keccak256_avx512_x8.S"
