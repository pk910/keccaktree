/*
 * void keccaktree_keccak256_zbb_x1(unsigned char *output,
 *                                  const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, one at a time in
 * the general registers (keccak256_rv64.inc) with the Zbb rotate and ANDN:
 * 145 instructions per round. Zbb is part of RVA22U64, so every current
 * application core has it (SiFive U74/P550, SpacemiT X60, SG2044 C920v2).
 */
#if defined(__riscv) && __riscv_xlen == 64
#define KECCAK_ZBB
#include "keccak256_riscv_frame.inc"
#include "keccak256_rv64.inc"

	.option		push
	.option		arch, +zbb
	KECCAK_X1	keccaktree_keccak256_zbb_x1
	.option		pop

	KECCAK_RC
	GNU_STACK_NOTE
#endif
