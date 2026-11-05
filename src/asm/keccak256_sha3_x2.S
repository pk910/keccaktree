/*
 * void keccaktree_keccak256_sha3_x2(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 2 at a time, with
 * the ARMv8.2 SHA3 instructions (Apple M-series, Neoverse V1/N2+, Graviton
 * 3+): EOR3 for the parities, RAX1 for theta's D, XAR for theta+rho in one
 * instruction per lane and BCAX for chi. 67 instructions per round, no
 * moves. The permutation is in keccak256_neon.inc.
 */
#ifdef __aarch64__
.arch armv8.2-a+sha3
#define KERNEL_NAME	keccaktree_keccak256_sha3_x2
#include "keccak256_arm_frame.inc"

.macro XOR3 d, a, b, c
	eor3		v\d\().16b, v\a\().16b, v\b\().16b, v\c\().16b
.endm

.macro PARITY c, a0, a1, a2, a3, a4
	eor3		v\c\().16b, v\a0\().16b, v\a1\().16b, v\a2\().16b
	eor3		v\c\().16b, v\c\().16b, v\a3\().16b, v\a4\().16b
.endm

.macro THETA_D d, c1, c2, t
	rax1		v\d\().2d, v\c1\().2d, v\c2\().2d
.endm

.macro RHO a, d, n, t
.if \n
	xar		v\a\().2d, v\a\().2d, v\d\().2d, #(64 - \n)
.else
	eor		v\a\().16b, v\a\().16b, v\d\().16b
.endif
.endm

/* XAR against v21, which is zero until round 0's last zero lane (21 itself)
 * is rotated into it */
.macro RHO_ZERO a, d, n, t
	xar		v\a\().2d, v21.2d, v\d\().2d, #(64 - \n)
.endm

/* bcax d, a, b, c: d = a ^ (b & ~c) */
.macro CHI_ROW b0, b1, b2, b3, b4, f0, f1
	bcax		v\f0\().16b, v\b0\().16b, v\b2\().16b, v\b1\().16b
	bcax		v\f1\().16b, v\b1\().16b, v\b3\().16b, v\b2\().16b
	bcax		v\b1\().16b, v\b4\().16b, v\b1\().16b, v\b0\().16b
	bcax		v\b0\().16b, v\b3\().16b, v\b0\().16b, v\b4\().16b
	bcax		v\b2\().16b, v\b2\().16b, v\b4\().16b, v\b3\().16b
.endm

#define FIRST_ROUND_SETUP movi v21.2d, #0
#include "keccak256_neon.inc"
	GNU_STACK_NOTE
#endif
