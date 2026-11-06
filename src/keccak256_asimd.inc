/*
 * Rounds of the ARMv8.0 Advanced SIMD kernels (keccak256_neon_x2.S,
 * keccak256_neon_x3.S), on the register scheme of keccak256_neon.inc.
 * Without FEAT_SHA3 a rotation is SHL + SRI into a fresh register and chi
 * is BIC + EOR: 160 instructions per round.
 *
 * As rho needs its source intact, a row's B[0..4] go to f0, f1, A0, A1, A2
 * (freeing A3, A4), so chi writes outputs 0 and 1 into A3, A4 and 2..4 over
 * A0, f0, f1; A1 and A2 are freed.
 *
 * Neoverse N1 (and Cortex-A76/A77/A78) run the vector shifts on one of
 * their two vector pipes only, so the shifts are what bounds these kernels
 * and every one that can be a plain ALU instruction is: theta's rotl(C, 1)
 * starts with ADD instead of SHL (+1.8% on N1) and the two lanes whose rho
 * rotation is a multiple of 8 (lanes 19 and 23) rotate with one TBL.
 *
 * The round is in pieces (THETA_C01, THETA_C234, THETA_DD, RHO_ROW,
 * CHI_ROW, ROUND_ROW4, the halves of FIRST_ROUND) so that
 * keccak256_neon_x3.S can interleave them with a scalar stream.
 */
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

/* d = c1 ^ rotl(c2, 1): the left shift by one is an ADD */
.macro THETA_D d, c1, c2, t
	add		v\t\().2d, v\c2\().2d, v\c2\().2d
	sri		v\t\().2d, v\c2\().2d, #63
	eor		v\d\().16b, v\t\().16b, v\c1\().16b
.endm

/* b = rotl(a ^ d, n), a is left with a ^ d; for n = 8 and 56 a byte
 * permutation (TBL, index vector loaded into the free register t) */
#ifndef ASIMD_TBL
#define ASIMD_TBL 1
#endif
.macro RHO b, a, d, n, t=0
.if (\n == 8 || \n == 56) && ASIMD_TBL
.if \t == 0
.error "RHO: byte rotation needs a scratch register"
.endif
	eor		v\a\().16b, v\a\().16b, v\d\().16b
	ldr		q\t, .LTBL\n
	tbl		v\b\().16b, {v\a\().16b}, v\t\().16b
.elseif \n
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

/* rho on one row into f0, f1, a0, a1, a2; then chi with a3, a4 free. The
 * TBL index of the fourth lane goes through a2 (free once the third
 * rotation has read it), that of the fifth through a3. */
.macro RHO_ROW a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, f0, f1
	RHO		\f0, \a0, \d0, \r0
	RHO		\f1, \a1, \d1, \r1
	RHO		\a0, \a2, \d2, \r2
	RHO		\a1, \a3, \d3, \r3, \a2
	RHO		\a2, \a4, \d4, \r4, \a3
.endm
.macro ROW a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, f0, f1
	RHO_ROW		\a0, \a1, \a2, \a3, \a4, \d0, \d1, \d2, \d3, \d4, \r0, \r1, \r2, \r3, \r4, \f0, \f1
	CHI_ROW		\f0, \f1, \a0, \a1, \a2, \a3, \a4
.endm

/* theta in pieces: the parities of columns 0..1, 2..4, then D */
.macro THETA_C01 ARGS
	PARITY		D1, \a0, \a5, \a10, \a15, \a20
	PARITY		D2, \a1, \a6, \a11, \a16, \a21
.endm
.macro THETA_C234 ARGS
	PARITY		D3, \a2, \a7, \a12, \a17, \a22
	PARITY		D4, \a3, \a8, \a13, \a18, \a23
	PARITY		\p, \a4, \a9, \a14, \a19, \a24
.endm
.macro THETA_DD ARGS
	THETA_D		D0, \p, D2, \q
	THETA_D		D2, D2, D4, \q
	THETA_D		D4, D4, D1, \q
	THETA_D		D1, D1, D3, \q
	THETA_D		D3, D3, \p, \q
.endm

/* Row y takes B[x] from lane ((x+3y)%5) + 5x; the pair a row frees is the
 * next row's f0, f1. Lane 0 of the new state is row 0's output 0 in a18;
 * the round constant is loaded into D0 once row 4's rho is done with it. */
.macro ROUND_ROW4 r, ARGS
	RHO_ROW		\a2, \a8, \a14, \a15, \a21, D2, D3, D4, D0, D1, 62, 55, 39, 41, 2, \a5, \a11
	ldr		q25, .LRC + 16*\r
	CHI_ROW		\a5, \a11, \a2, \a8, \a14, \a15, \a21
	eor		v\a18\().16b, v\a18\().16b, v25.16b
.endm
.macro ROUND r, ARGS
	THETA		PASS
	ROW		\a0, \a6, \a12, \a18, \a24, D0, D1, D2, D3, D4, 0, 44, 43, 21, 14, \p, \q
	ROW		\a3, \a9, \a10, \a16, \a22, D3, D4, D0, D1, D2, 28, 20, 3, 45, 61, \a6, \a12
	ROW		\a1, \a7, \a13, \a19, \a20, D1, D2, D3, D4, D0, 1, 6, 25, 8, 18, \a9, \a10
	ROW		\a4, \a5, \a11, \a17, \a23, D4, D0, D1, D2, D3, 27, 36, 10, 15, 56, \a7, \a13
	ROUND_ROW4	\r, PASS
.endm

/* round 0 on the state lane i = v(i): input words in v0..v7, 0x01 in v8,
 * 0x80..0 in v16, the rest zero (not initialised; RHO_ZERO ignores them).
 * In two halves: theta with rows 0..1, then rows 2..4. */
.macro FIRST_ROUND_A
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
.endm
.macro FIRST_ROUND_B
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
.macro FIRST_ROUND
	FIRST_ROUND_A
	FIRST_ROUND_B
.endm

/* round 23 after theta: row 0, x = 0..3 only (chi's fifth output is two
 * spare instructions). The digests end up in v25, v26 (node 0) and v27,
 * v28 (node 1), ready to store. */
.macro LAST_ROW ARGS
	ROW		\a0, \a6, \a12, \a18, \a24, D0, D1, D2, D3, D4, 0, 44, 43, 21, 14, \p, \q
	IOTA		\a18, 23, D0
	zip1		v25.2d, v\a18\().2d, v\a24\().2d
	zip1		v26.2d, v\a0\().2d, v\p\().2d
	zip2		v27.2d, v\a18\().2d, v\a24\().2d
	zip2		v28.2d, v\a0\().2d, v\p\().2d
.endm
.macro LAST_ROUND ARGS
	THETA		PASS
	LAST_ROW	PASS
.endm

/* TBL indices of the byte rotations: rotl by 8 and by 56 in each 64-bit
 * lane (after KECCAK_RC, which the kernels place after their code) */
.macro ASIMD_TABLES
.p2align 4
.LTBL8:	.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
.LTBL56:	.byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8
.endm
