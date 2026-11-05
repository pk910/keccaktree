/*
 * Rounds of the FEAT_SHA3 vector kernels (keccak256_sha3_x2.S,
 * keccak256_sha3_x3.S), on the register scheme of keccak256_neon.inc: EOR3
 * for the parities, RAX1 for theta's D, XAR for theta+rho in one
 * instruction per lane and BCAX for chi. 67 instructions per round, no
 * moves. Rho rotates in place, so a row's chi writes outputs 0 and 1 into
 * the free pair and 2..4 over B[2], B[0], B[1]; B[3] and B[4] are freed.
 */
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

/* XAR against v21, which round 0 starts as zero: its last zero lane is
 * 21 itself */
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

/* rho on one row: b = rotl(a ^ d, r) in place; t scratch */
.macro RHO_ROW a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, t
	RHO		\a0, \d0, \r0, \t
	RHO		\a1, \d1, \r1, \t
	RHO		\a2, \d2, \r2, \t
	RHO		\a3, \d3, \r3, \t
	RHO		\a4, \d4, \r4, \t
.endm

/* rho and chi on one row; f0, f1 free */
.macro ROW a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, f0, f1
	RHO_ROW		\a0, \a1, \a2, \a3, \a4, \d0, \d1, \d2, \d3, \d4, \r0, \r1, \r2, \r3, \r4, \f1
	CHI_ROW		\a0, \a1, \a2, \a3, \a4, \f0, \f1
.endm

/* Row y takes B[x] from lane ((x+3y)%5) + 5x. The two registers freed by a
 * row's chi receive the next row's first two outputs; the iota load goes
 * into one of them while row 1 rotates. The rows are split so that
 * keccak256_sha3_x3.S can interleave a scalar stream between them. */
.macro ROUND_ROWS01 r, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, p, q
	ROW		\a0, \a6, \a12, \a18, \a24, D0, D1, D2, D3, D4, 0, 44, 43, 21, 14, \p, \q
	ldr		q\a18, .LRC + 16*\r
	RHO_ROW		\a3, \a9, \a10, \a16, \a22, D3, D4, D0, D1, D2, 28, 20, 3, 45, 61, \a24
	eor		v\p\().16b, v\p\().16b, v\a18\().16b
	CHI_ROW		\a3, \a9, \a10, \a16, \a22, \a18, \a24
.endm
.macro ROUND_ROW2 a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, p, q
	ROW		\a1, \a7, \a13, \a19, \a20, D1, D2, D3, D4, D0, 1, 6, 25, 8, 18, \a16, \a22
.endm
.macro ROUND_ROW3 a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, p, q
	ROW		\a4, \a5, \a11, \a17, \a23, D4, D0, D1, D2, D3, 27, 36, 10, 15, 56, \a19, \a20
.endm
.macro ROUND_ROW4 a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, p, q
	ROW		\a2, \a8, \a14, \a15, \a21, D2, D3, D4, D0, D1, 62, 55, 39, 41, 2, \a17, \a23
.endm

.macro ROUND r, ARGS
	THETA		PASS
	ROUND_ROWS01	\r, PASS
	ROUND_ROW2	PASS
	ROUND_ROW3	PASS
	ROUND_ROW4	PASS
.endm

/* round 0 on the state lane i = v(i): input words in v0..v7, 0x01 in v8,
 * 0x80..0 in v16, the rest zero (not initialised; RHO_ZERO sets them) */
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
	RHO		0, D0, 0, 31
	RHO		6, D1, 44, 31
	RHO_ZERO	12, D2, 43, 31
	RHO_ZERO	18, D3, 21, 31
	RHO_ZERO	24, D4, 14, 31
	CHI_ROW		0, 6, 12, 18, 24, 30, 31
	ldr		q18, .LRC
	RHO		3, D3, 28, 24
	RHO_ZERO	9, D4, 20, 24
	RHO_ZERO	10, D0, 3, 24
	RHO		16, D1, 45, 24
	RHO_ZERO	22, D2, 61, 24
	eor		v30.16b, v30.16b, v18.16b
	CHI_ROW		3, 9, 10, 16, 22, 18, 24
	RHO		1, D1, 1, 22
	RHO		7, D2, 6, 22
	RHO_ZERO	13, D3, 25, 22
	RHO_ZERO	19, D4, 8, 22
	RHO_ZERO	20, D0, 18, 22
	CHI_ROW		1, 7, 13, 19, 20, 16, 22
	RHO		4, D4, 27, 20
	RHO		5, D0, 36, 20
	RHO_ZERO	11, D1, 10, 20
	RHO_ZERO	17, D2, 15, 20
	RHO_ZERO	23, D3, 56, 20
	CHI_ROW		4, 5, 11, 17, 23, 19, 20
	RHO		2, D2, 62, 23
	RHO		8, D3, 55, 23
	RHO_ZERO	14, D4, 39, 23
	RHO_ZERO	15, D0, 41, 23
	RHO_ZERO	21, D1, 2, 23
	CHI_ROW		2, 8, 14, 15, 21, 17, 23
.endm

/* round 23: row 0, x = 0..3 only. The digests end up in v25, v26 (node
 * 0) and v27, v28 (node 1), ready to store. */
.macro LAST_ROUND ARGS
	THETA		PASS
	ROW		\a0, \a6, \a12, \a18, \a24, D0, D1, D2, D3, D4, 0, 44, 43, 21, 14, \p, \q
	IOTA		\p, 23, D0
	zip1		v25.2d, v\p\().2d, v\q\().2d
	zip1		v26.2d, v\a12\().2d, v\a0\().2d
	zip2		v27.2d, v\p\().2d, v\q\().2d
	zip2		v28.2d, v\a12\().2d, v\a0\().2d
.endm

/* rounds 0..23: lanes of the input in v0..v7 (LOAD_X2), the digests in
 * v25..v28 */
.macro PERMUTATION
	movi		v21.2d, #0
	FIRST_ROUND
	ROUND		1, 30, 31, 12, 0, 6, 18, 24, 10, 3, 9, 16, 22, 13, 1, 7, 19, 20, 11, 4, 5, 17, 23, 14, 2, 8, 15, 21
	ROUND		2, 15, 21, 13, 30, 24, 4, 8, 16, 0, 9, 20, 14, 1, 31, 10, 5, 17, 22, 6, 18, 11, 2, 7, 12, 3, 19, 23
	ROUND		3, 19, 23, 1, 15, 8, 6, 3, 20, 30, 9, 17, 7, 31, 21, 16, 18, 11, 14, 24, 4, 22, 12, 10, 13, 0, 5, 2
	ROUND		4, 5, 2, 31, 19, 3, 24, 0, 17, 15, 9, 11, 10, 21, 23, 20, 4, 22, 7, 8, 6, 14, 13, 16, 1, 30, 18, 12
	ROUND		5, 18, 12, 21, 5, 0, 8, 30, 11, 19, 9, 22, 16, 23, 2, 17, 6, 14, 10, 3, 24, 7, 1, 20, 31, 15, 4, 13
	ROUND		6, 4, 13, 23, 18, 30, 3, 15, 22, 5, 9, 14, 20, 2, 12, 11, 24, 7, 16, 0, 8, 10, 31, 17, 21, 19, 6, 1
	ROUND		7, 6, 1, 2, 4, 15, 0, 19, 14, 18, 9, 7, 17, 12, 13, 22, 8, 10, 20, 30, 3, 16, 21, 11, 23, 5, 24, 31
	ROUND		8, 24, 31, 12, 6, 19, 30, 5, 7, 4, 9, 10, 11, 13, 1, 14, 3, 16, 17, 15, 0, 20, 23, 22, 2, 18, 8, 21
	ROUND		9, 8, 21, 13, 24, 5, 15, 18, 10, 6, 9, 16, 22, 1, 31, 7, 0, 20, 11, 19, 30, 17, 2, 14, 12, 4, 3, 23
	ROUND		10, 3, 23, 1, 8, 18, 19, 4, 16, 24, 9, 20, 14, 31, 21, 10, 30, 17, 22, 5, 15, 11, 12, 7, 13, 6, 0, 2
	ROUND		11, 0, 2, 31, 3, 4, 5, 6, 20, 8, 9, 17, 7, 21, 23, 16, 15, 11, 14, 18, 19, 22, 13, 10, 1, 24, 30, 12
	ROUND		12, 30, 12, 21, 0, 6, 18, 24, 17, 3, 9, 11, 10, 23, 2, 20, 19, 22, 7, 4, 5, 14, 1, 16, 31, 8, 15, 13
	ROUND		13, 15, 13, 23, 30, 24, 4, 8, 11, 0, 9, 22, 16, 2, 12, 17, 5, 14, 10, 6, 18, 7, 31, 20, 21, 3, 19, 1
	ROUND		14, 19, 1, 2, 15, 8, 6, 3, 22, 30, 9, 14, 20, 12, 13, 11, 18, 7, 16, 24, 4, 10, 21, 17, 23, 0, 5, 31
	ROUND		15, 5, 31, 12, 19, 3, 24, 0, 14, 15, 9, 7, 17, 13, 1, 22, 4, 10, 20, 8, 6, 16, 23, 11, 2, 30, 18, 21
	ROUND		16, 18, 21, 13, 5, 0, 8, 30, 7, 19, 9, 10, 11, 1, 31, 14, 6, 16, 17, 3, 24, 20, 2, 22, 12, 15, 4, 23
	ROUND		17, 4, 23, 1, 18, 30, 3, 15, 10, 5, 9, 16, 22, 31, 21, 7, 24, 20, 11, 0, 8, 17, 12, 14, 13, 19, 6, 2
	ROUND		18, 6, 2, 31, 4, 15, 0, 19, 16, 18, 9, 20, 14, 21, 23, 10, 8, 17, 22, 30, 3, 11, 13, 7, 1, 5, 24, 12
	ROUND		19, 24, 12, 21, 6, 19, 30, 5, 20, 4, 9, 17, 7, 23, 2, 16, 3, 11, 14, 15, 0, 22, 1, 10, 31, 18, 8, 13
	ROUND		20, 8, 13, 23, 24, 5, 15, 18, 17, 6, 9, 11, 10, 2, 12, 20, 0, 22, 7, 19, 30, 14, 31, 16, 21, 4, 3, 1
	ROUND		21, 3, 1, 2, 8, 18, 19, 4, 11, 24, 9, 22, 16, 12, 13, 17, 30, 14, 10, 5, 15, 7, 21, 20, 23, 6, 0, 31
	ROUND		22, 0, 31, 12, 3, 4, 5, 6, 22, 8, 9, 14, 20, 13, 1, 11, 15, 7, 16, 18, 19, 10, 23, 17, 2, 24, 30, 21
	LAST_ROUND	30, 21, 13, 0, 6, 18, 24, 14, 3, 9, 7, 17, 1, 31, 22, 19, 10, 20, 4, 5, 16, 2, 11, 12, 8, 15, 23
.endm
