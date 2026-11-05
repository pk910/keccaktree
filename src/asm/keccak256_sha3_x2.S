/*
 * void keccaktree_keccak256_sha3_x2(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 2 at a time, with
 * the ARMv8.2 SHA3 instructions (Apple M-series, Neoverse V1/N2+, Graviton
 * 3+). The permutation is in keccak256_neon.inc and keccak256_sha3.inc.
 */
#ifdef __aarch64__
.arch armv8.2-a+sha3
#include "keccak256_arm_frame.inc"
#include "keccak256_neon.inc"
#include "keccak256_sha3.inc"

	X2_FUNCTION keccaktree_keccak256_sha3_x2
	GNU_STACK_NOTE
#endif
