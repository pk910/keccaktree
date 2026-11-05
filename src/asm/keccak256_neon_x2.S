/*
 * void keccaktree_keccak256_neon_x2(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 2 at a time, in
 * ARMv8.0 Advanced SIMD (Cortex-A5x/A7x, Neoverse N1, Graviton 2). Without
 * FEAT_SHA3 a rotation is USHR + SHL + ORR and chi is BIC + EOR: 160
 * instructions per round. The permutation is in keccak256_neon.inc.
 */
#ifdef __aarch64__
#define KERNEL_NAME	keccaktree_keccak256_neon_x2
#include "keccak256_arm_frame.inc"

.macro XOR3 d, a, b, c
	eor		v\d\().16b, v\a\().16b, v\b\().16b
	eor		v\d\().16b, v\d\().16b, v\c\().16b
.endm

.macro PARITY c, a0, a1, a2, a3, a4
	eor		v\c\().16b, v\a0\().16b, v\a1\().16b
	eor		v\c\().16b, v\c\().16b, v\a2\().16b
	eor		v\c\().16b, v\c\().16b, v\a3\().16b
	eor		v\c\().16b, v\c\().16b, v\a4\().16b
.endm

.macro THETA_D d, c1, c2, t
	shl		v\t\().2d, v\c2\().2d, #1
	sri		v\t\().2d, v\c2\().2d, #63
	eor		v\d\().16b, v\t\().16b, v\c1\().16b
.endm

.macro RHO a, d, n, t
	eor		v\a\().16b, v\a\().16b, v\d\().16b
.if \n
	ushr		v\t\().2d, v\a\().2d, #(64 - \n)
	shl		v\a\().2d, v\a\().2d, #\n
	orr		v\a\().16b, v\a\().16b, v\t\().16b
.endif
.endm

.macro RHO_ZERO a, d, n, t
	ushr		v\t\().2d, v\d\().2d, #(64 - \n)
	shl		v\a\().2d, v\d\().2d, #\n
	orr		v\a\().16b, v\a\().16b, v\t\().16b
.endm

/* bic d, a, b: d = a & ~b. Outputs 3 and 4 are built in place: each
 * input's last use is the BIC that starts the output taking its place. */
.macro CHI_ROW b0, b1, b2, b3, b4, f0, f1
	bic		v\f1\().16b, v\b2\().16b, v\b1\().16b
	eor		v\f0\().16b, v\b0\().16b, v\f1\().16b
	bic		v\f1\().16b, v\b3\().16b, v\b2\().16b
	eor		v\f1\().16b, v\b1\().16b, v\f1\().16b
	bic		v\b1\().16b, v\b1\().16b, v\b0\().16b
	bic		v\b0\().16b, v\b0\().16b, v\b4\().16b
	eor		v\b0\().16b, v\b3\().16b, v\b0\().16b
	eor		v\b1\().16b, v\b4\().16b, v\b1\().16b
	bic		v\b3\().16b, v\b4\().16b, v\b3\().16b
	eor		v\b2\().16b, v\b2\().16b, v\b3\().16b
.endm

#define FIRST_ROUND_SETUP
#include "keccak256_neon.inc"
	GNU_STACK_NOTE
#endif
