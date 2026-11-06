/*
 * void keccaktree_keccak256_rvv(unsigned char *output,
 *                               const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, VLEN/64 at a time
 * with RVV 1.0 (keccak256_rvv.inc), rotations as shift pairs and ANDN as
 * VNOT + VAND: 214 vector instructions per round per batch.
 */
#if defined(__riscv) && __riscv_xlen == 64
#include "keccak256_riscv_frame.inc"
#include "keccak256_rvv.inc"

	.option		push
	.option		arch, +v
	KECCAK_RVV	keccaktree_keccak256_rvv
	.option		pop

	KECCAK_RC
	GNU_STACK_NOTE
#endif
