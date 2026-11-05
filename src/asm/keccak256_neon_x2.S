/*
 * void keccaktree_keccak256_neon_x2(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 2 at a time, in
 * ARMv8.0 Advanced SIMD (Cortex-A5x/A7x, Neoverse N1, Graviton 2), on the
 * register scheme of keccak256_neon.inc. Without FEAT_SHA3 a rotation is
 * SHL + SRI into a fresh register and chi is BIC + EOR: 160 instructions
 * per round.
 *
 * As rho needs its source intact, a row's B[0..4] go to f0, f1, A0, A1, A2
 * (freeing A3, A4), so chi writes outputs 0 and 1 into A3, A4 and 2..4 over
 * A0, f0, f1; A1 and A2 are freed.
 */
#ifdef __aarch64__
#include "keccak256_arm_frame.inc"
#include "keccak256_neon.inc"

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

/* b = rotl(a ^ d, n), a is left with a ^ d */
.macro RHO b, a, d, n
.if \n
	eor		v\a\().16b, v\a\().16b, v\d\().16b
	shl		v\b\().2d, v\a\().2d, #\n
	sri		v\b\().2d, v\a\().2d, #(64 - \n)
.else
	eor		v\b\().16b, v\a\().16b, v\d\().16b
.endif
.endm

/* b = rotl(d, n), for a zero lane in round 0 */
.macro RHO_ZERO b, d, n
	shl		v\b\().2d, v\d\().2d, #\n
	sri		v\b\().2d, v\d\().2d, #(64 - \n)
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

/* rho on one row into f0, f1, a0, a1, a2; then chi with a3, a4 free */
.macro RHO_ROW a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, f0, f1
	RHO		\f0, \a0, \d0, \r0
	RHO		\f1, \a1, \d1, \r1
	RHO		\a0, \a2, \d2, \r2
	RHO		\a1, \a3, \d3, \r3
	RHO		\a2, \a4, \d4, \r4
.endm
.macro ROW a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, f0, f1
	RHO_ROW		\a0, \a1, \a2, \a3, \a4, \d0, \d1, \d2, \d3, \d4, \r0, \r1, \r2, \r3, \r4, \f0, \f1
	CHI_ROW		\f0, \f1, \a0, \a1, \a2, \a3, \a4
.endm

/* Row y takes B[x] from lane ((x+3y)%5) + 5x; the pair a row frees is the
 * next row's f0, f1. Lane 0 of the new state is row 0's output 0 in a18;
 * the round constant is loaded into D0 once row 4's rho is done with it. */
.macro ROUND r, ARGS
	THETA		PASS
	ROW		\a0, \a6, \a12, \a18, \a24, D0, D1, D2, D3, D4, 0, 44, 43, 21, 14, \p, \q
	ROW		\a3, \a9, \a10, \a16, \a22, D3, D4, D0, D1, D2, 28, 20, 3, 45, 61, \a6, \a12
	ROW		\a1, \a7, \a13, \a19, \a20, D1, D2, D3, D4, D0, 1, 6, 25, 8, 18, \a9, \a10
	ROW		\a4, \a5, \a11, \a17, \a23, D4, D0, D1, D2, D3, 27, 36, 10, 15, 56, \a7, \a13
	RHO_ROW		\a2, \a8, \a14, \a15, \a21, D2, D3, D4, D0, D1, 62, 55, 39, 41, 2, \a5, \a11
	ldr		q25, .LRC + 16*\r
	CHI_ROW		\a5, \a11, \a2, \a8, \a14, \a15, \a21
	eor		v\a18\().16b, v\a18\().16b, v25.16b
.endm

/* round 0 on the state lane i = v(i): input words in v0..v7, 0x01 in v8,
 * 0x80..0 in v16, the rest zero (not initialised; RHO_ZERO ignores them) */
.macro FIRST_ROUND
	eor		v26.16b, v0.16b, v5.16b
	XOR3		27, 1, 6, 16
	eor		v28.16b, v2.16b, v7.16b
	eor		v29.16b, v3.16b, v8.16b
	mov		v30.16b, v4.16b
	THETA_D		D0, 30, D2, 31
	THETA_D		D2, D2, D4, 31
	THETA_D		D4, D4, D1, 31
	THETA_D		D1, D1, D3, 31
	THETA_D		D3, D3, 30, 31
	RHO		30, 0, D0, 0
	RHO		31, 6, D1, 44
	RHO_ZERO	0, D2, 43
	RHO_ZERO	6, D3, 21
	RHO_ZERO	12, D4, 14
	CHI_ROW		30, 31, 0, 6, 12, 18, 24
	RHO		6, 3, D3, 28
	RHO_ZERO	12, D4, 20
	RHO_ZERO	3, D0, 3
	RHO		9, 16, D1, 45
	RHO_ZERO	10, D2, 61
	CHI_ROW		6, 12, 3, 9, 10, 16, 22
	RHO		9, 1, D1, 1
	RHO		10, 7, D2, 6
	RHO_ZERO	1, D3, 25
	RHO_ZERO	7, D4, 8
	RHO_ZERO	13, D0, 18
	CHI_ROW		9, 10, 1, 7, 13, 19, 20
	RHO		7, 4, D4, 27
	RHO		13, 5, D0, 36
	RHO_ZERO	4, D1, 10
	RHO_ZERO	5, D2, 15
	RHO_ZERO	11, D3, 56
	CHI_ROW		7, 13, 4, 5, 11, 17, 23
	RHO		5, 2, D2, 62
	RHO		11, 8, D3, 55
	RHO_ZERO	2, D4, 39
	RHO_ZERO	8, D0, 41
	RHO_ZERO	14, D1, 2
	ldr		q25, .LRC
	CHI_ROW		5, 11, 2, 8, 14, 15, 21
	eor		v18.16b, v18.16b, v25.16b
.endm

/* round 23: row 0, x = 0..3 only (chi's fifth output is two spare
 * instructions). The digests end up in v25, v26 (node 0) and v27, v28
 * (node 1), ready to store. */
.macro LAST_ROUND ARGS
	THETA		PASS
	ROW		\a0, \a6, \a12, \a18, \a24, D0, D1, D2, D3, D4, 0, 44, 43, 21, 14, \p, \q
	IOTA		\a18, 23, D0
	zip1		v25.2d, v\a18\().2d, v\a24\().2d
	zip1		v26.2d, v\a0\().2d, v\p\().2d
	zip2		v27.2d, v\a18\().2d, v\a24\().2d
	zip2		v28.2d, v\a0\().2d, v\p\().2d
.endm

/* rounds 0..23: lanes of the input in v0..v7 (LOAD_X2), the digests in
 * v25..v28 */
.macro PERMUTATION
	FIRST_ROUND
	ROUND		1, 18, 24, 0, 30, 31, 16, 22, 3, 6, 12, 19, 20, 1, 9, 10, 17, 23, 4, 7, 13, 15, 21, 2, 5, 11, 8, 14
	ROUND		2, 7, 11, 18, 8, 14, 23, 2, 30, 22, 1, 13, 15, 24, 12, 19, 4, 5, 31, 3, 9, 17, 21, 0, 16, 20, 6, 10
	ROUND		3, 3, 20, 7, 6, 10, 5, 0, 8, 2, 24, 9, 17, 11, 1, 13, 31, 16, 14, 30, 12, 4, 21, 18, 23, 15, 22, 19
	ROUND		4, 30, 15, 3, 22, 19, 16, 18, 6, 0, 11, 12, 4, 20, 24, 9, 14, 23, 10, 8, 1, 31, 21, 7, 5, 17, 2, 13
	ROUND		5, 8, 17, 30, 2, 13, 23, 7, 22, 18, 20, 1, 31, 15, 11, 12, 10, 5, 19, 6, 24, 14, 21, 3, 16, 4, 0, 9
	ROUND		6, 6, 4, 8, 0, 9, 5, 3, 2, 7, 15, 24, 14, 17, 20, 1, 19, 16, 13, 22, 11, 10, 21, 30, 23, 31, 18, 12
	ROUND		7, 22, 31, 6, 18, 12, 16, 30, 0, 3, 17, 11, 10, 4, 15, 24, 13, 23, 9, 2, 20, 19, 21, 8, 5, 14, 7, 1
	ROUND		8, 2, 14, 22, 7, 1, 23, 8, 18, 30, 4, 20, 19, 31, 17, 11, 9, 5, 12, 0, 15, 13, 21, 6, 16, 10, 3, 24
	ROUND		9, 0, 10, 2, 3, 24, 5, 6, 7, 8, 31, 15, 13, 14, 4, 20, 12, 16, 1, 18, 17, 9, 21, 22, 23, 19, 30, 11
	ROUND		10, 18, 19, 0, 30, 11, 16, 22, 3, 6, 14, 17, 9, 10, 31, 15, 1, 23, 24, 7, 4, 12, 21, 2, 5, 13, 8, 20
	ROUND		11, 7, 13, 18, 8, 20, 23, 2, 30, 22, 10, 4, 12, 19, 14, 17, 24, 5, 11, 3, 31, 1, 21, 0, 16, 9, 6, 15
	ROUND		12, 3, 9, 7, 6, 15, 5, 0, 8, 2, 19, 31, 1, 13, 10, 4, 11, 16, 20, 30, 14, 24, 21, 18, 23, 12, 22, 17
	ROUND		13, 30, 12, 3, 22, 17, 16, 18, 6, 0, 13, 14, 24, 9, 19, 31, 20, 23, 15, 8, 10, 11, 21, 7, 5, 1, 2, 4
	ROUND		14, 8, 1, 30, 2, 4, 23, 7, 22, 18, 9, 10, 11, 12, 13, 14, 15, 5, 17, 6, 19, 20, 21, 3, 16, 24, 0, 31
	ROUND		15, 6, 24, 8, 0, 31, 5, 3, 2, 7, 12, 19, 20, 1, 9, 10, 17, 16, 4, 22, 13, 15, 21, 30, 23, 11, 18, 14
	ROUND		16, 22, 11, 6, 18, 14, 16, 30, 0, 3, 1, 13, 15, 24, 12, 19, 4, 23, 31, 2, 9, 17, 21, 8, 5, 20, 7, 10
	ROUND		17, 2, 20, 22, 7, 10, 23, 8, 18, 30, 24, 9, 17, 11, 1, 13, 31, 5, 14, 0, 12, 4, 21, 6, 16, 15, 3, 19
	ROUND		18, 0, 15, 2, 3, 19, 5, 6, 7, 8, 11, 12, 4, 20, 24, 9, 14, 16, 10, 18, 1, 31, 21, 22, 23, 17, 30, 13
	ROUND		19, 18, 17, 0, 30, 13, 16, 22, 3, 6, 20, 1, 31, 15, 11, 12, 10, 23, 19, 7, 24, 14, 21, 2, 5, 4, 8, 9
	ROUND		20, 7, 4, 18, 8, 9, 23, 2, 30, 22, 15, 24, 14, 17, 20, 1, 19, 5, 13, 3, 11, 10, 21, 0, 16, 31, 6, 12
	ROUND		21, 3, 31, 7, 6, 12, 5, 0, 8, 2, 17, 11, 10, 4, 15, 24, 13, 16, 9, 30, 20, 19, 21, 18, 23, 14, 22, 1
	ROUND		22, 30, 14, 3, 22, 1, 16, 18, 6, 0, 4, 20, 19, 31, 17, 11, 9, 23, 12, 8, 15, 13, 21, 7, 5, 10, 2, 24
	LAST_ROUND	8, 10, 30, 2, 24, 23, 7, 22, 18, 31, 15, 13, 14, 4, 20, 12, 5, 1, 6, 17, 9, 21, 3, 16, 19, 0, 11
.endm

	X2_FUNCTION keccaktree_keccak256_neon_x2
	GNU_STACK_NOTE
#endif
