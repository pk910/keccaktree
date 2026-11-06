/*
 * void keccaktree_keccak256_rv64_x1(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, one at a time in
 * the general registers (keccak256_rv64.inc), base RV64I only: rotations
 * are shift pairs and ANDN is NOT + AND. For cores without Zbb.
 */
#if defined(__riscv) && __riscv_xlen == 64
#include "keccak256_riscv_frame.inc"
#include "keccak256_rv64.inc"

	KECCAK_X1	keccaktree_keccak256_rv64_x1

	KECCAK_RC
	GNU_STACK_NOTE
#endif
