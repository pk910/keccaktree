/*
 * Keccak-f[1600] on one node in the general registers with explicit
 * rotations, the scalar stream of keccak256_sha3_x3r.S (Apple cores).
 *
 * keccak256_scalar.inc never rotates and instead folds rho into the ROR
 * operand of every EOR/BIC. Apple's cores run a shifted-operand EOR/BIC at
 * 2 cycles latency on only half of their integer pipes, so here the lanes
 * are rotated in place with ROR (1 cycle, every pipe) and EOR/BIC are plain.
 * Only theta's D = C[x-1] ^ rotl(C[x+1], 1) keeps 9 shifted operands.
 * 130 instructions per round.
 *
 * Registers and the pi renaming are the same as in keccak256_scalar.inc:
 * the 25 lanes plus five for the column parities C0..C4, which turn into
 * D0..D3 (D4 is not formed: the five lanes of column 4 take C3 ^ rotl(C0, 1)
 * in two EORs each, which keeps the state in 30 registers and leaves x18
 * alone for macOS). Each round's line names every lane's register; chi
 * writes two lanes into free registers and the rest over their inputs.
 *
 * The including file sets OUT_SLOT (stack offset of the saved output
 * pointer) and OUT_OFF (byte offset of this node's digest).
 */

/* rho rotation of lane i */
.set R0, 0
.set R1, 1
.set R2, 62
.set R3, 28
.set R4, 27
.set R5, 36
.set R6, 44
.set R7, 6
.set R8, 55
.set R9, 20
.set R10, 3
.set R11, 10
.set R12, 43
.set R13, 25
.set R14, 39
.set R15, 41
.set R16, 45
.set R17, 15
.set R18, 21
.set R19, 8
.set R20, 18
.set R21, 2
.set R22, 61
.set R23, 56
.set R24, 14

/* a = rotl(a, n) in place; b = rotl(a, n) */
.macro SROL a, n
.if \n
	ror		x\a, x\a, #(64 - \n)
.endif
.endm
.macro SROL2 b, a, n
	ror		x\b, x\a, #((64 - \n) & 63)
.endm

/* a = rotl(a ^ d, n): theta and rho on one lane */
.macro SRHO1 a, d, n
	eor		x\a, x\a, x\d
	SROL		\a, \n
.endm

#define SARGS s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, c0, c1, c2, c3, c4
#define SPASS \s0, \s1, \s2, \s3, \s4, \s5, \s6, \s7, \s8, \s9, \s10, \s11, \s12, \s13, \s14, \s15, \s16, \s17, \s18, \s19, \s20, \s21, \s22, \s23, \s24, \c0, \c1, \c2, \c3, \c4

/* parities C0..C4, column 4 of the state updated with D4 = C3 ^ rotl(C0, 1)
 * and rotated, then D1, D3, D0, D2 over c0, c2, c4, c1 in that order (each
 * C's last use first); c3 is free */
/* SCALAR_ROR_D4_SPILL 1: lane 2 is stored to [sp, #SPILL_SLOT] and its
 * register forms D4, so column 4 takes one plain EOR per lane: 6 ALU
 * instructions and a store/load pair instead of 10 ALU instructions
 * (round 23 only needs lane 24 of that column, 12 fewer there). Set by
 * keccak256_sha3_x3r_sp.S. */
#ifndef SCALAR_ROR_D4_SPILL
#define SCALAR_ROR_D4_SPILL 0
#endif
.macro STHETA_PARITY SARGS
	eor		x\c0, x\s0, x\s5
	eor		x\c1, x\s1, x\s6
	eor		x\c2, x\s2, x\s7
	eor		x\c3, x\s3, x\s8
	eor		x\c4, x\s4, x\s9
	eor		x\c0, x\c0, x\s10
	eor		x\c1, x\c1, x\s11
	eor		x\c2, x\c2, x\s12
	eor		x\c3, x\c3, x\s13
	eor		x\c4, x\c4, x\s14
	eor		x\c0, x\c0, x\s15
	eor		x\c1, x\c1, x\s16
	eor		x\c2, x\c2, x\s17
	eor		x\c3, x\c3, x\s18
	eor		x\c4, x\c4, x\s19
	eor		x\c0, x\c0, x\s20
	eor		x\c1, x\c1, x\s21
	eor		x\c2, x\c2, x\s22
	eor		x\c3, x\c3, x\s23
	eor		x\c4, x\c4, x\s24
.endm
/* D1, D3, D0, D2 over c0, c2, c4, c1 (each C's last use first); c3 free */
.macro STHETA_D SARGS
	eor		x\c0, x\c0, x\c2, ror #63
	eor		x\c2, x\c2, x\c4, ror #63
	eor		x\c4, x\c4, x\c1, ror #63
	eor		x\c1, x\c1, x\c3, ror #63
.endm
.macro STHETA SARGS
#if SCALAR_ROR_D4_SPILL
	str		x\s2, [sp, #SPILL_SLOT]
	STHETA_PARITY	SPASS
	eor		x\s2, x\c3, x\c0, ror #63
	eor		x\s4, x\s4, x\s2
	eor		x\s9, x\s9, x\s2
	eor		x\s14, x\s14, x\s2
	eor		x\s19, x\s19, x\s2
	eor		x\s24, x\s24, x\s2
	STHETA_D	SPASS
	ldr		x\s2, [sp, #SPILL_SLOT]
#else
	STHETA_PARITY	SPASS
	eor		x\s4, x\s4, x\c3
	eor		x\s9, x\s9, x\c3
	eor		x\s14, x\s14, x\c3
	eor		x\s19, x\s19, x\c3
	eor		x\s24, x\s24, x\c3
	eor		x\s4, x\s4, x\c0, ror #63
	eor		x\s9, x\s9, x\c0, ror #63
	eor		x\s14, x\s14, x\c0, ror #63
	eor		x\s19, x\s19, x\c0, ror #63
	eor		x\s24, x\s24, x\c0, ror #63
	STHETA_D	SPASS
#endif
	SROL		\s4, R4
	SROL		\s9, R9
	SROL		\s14, R14
	SROL		\s19, R19
	SROL		\s24, R24
.endm
/* round 23: only lane 24 of column 4 is needed (row 0, x = 0..3) */
.macro STHETA_LAST SARGS
#if SCALAR_ROR_D4_SPILL
	STHETA_PARITY	SPASS
	eor		x\s2, x\c3, x\c0, ror #63
	eor		x\s24, x\s24, x\s2
	STHETA_D	SPASS
	SROL		\s24, R24
#else
	STHETA		SPASS
#endif
.endm

/* theta and rho on columns 0..3: D0 in c4, D1 in c0, D2 in c1, D3 in c2 */
.macro SRHO SARGS
	SRHO1		\s0, \c4, R0
	SRHO1		\s1, \c0, R1
	SRHO1		\s2, \c1, R2
	SRHO1		\s3, \c2, R3
	SRHO1		\s5, \c4, R5
	SRHO1		\s6, \c0, R6
	SRHO1		\s7, \c1, R7
	SRHO1		\s8, \c2, R8
	SRHO1		\s10, \c4, R10
	SRHO1		\s11, \c0, R11
	SRHO1		\s12, \c1, R12
	SRHO1		\s13, \c2, R13
	SRHO1		\s15, \c4, R15
	SRHO1		\s16, \c0, R16
	SRHO1		\s17, \c1, R17
	SRHO1		\s18, \c2, R18
	SRHO1		\s20, \c4, R20
	SRHO1		\s21, \c0, R21
	SRHO1		\s22, \c1, R22
	SRHO1		\s23, \c2, R23
.endm

/* STHETA in two pieces (parities; the rest), SRHO in two halves, for
 * finer interleaving (keccak256_sha3_x3rp.S) */
.macro STHETA_REST SARGS
#if SCALAR_ROR_D4_SPILL
	eor		x\s2, x\c3, x\c0, ror #63
	eor		x\s4, x\s4, x\s2
	eor		x\s9, x\s9, x\s2
	eor		x\s14, x\s14, x\s2
	eor		x\s19, x\s19, x\s2
	eor		x\s24, x\s24, x\s2
	STHETA_D	SPASS
	ldr		x\s2, [sp, #SPILL_SLOT]
#else
	eor		x\s4, x\s4, x\c3
	eor		x\s9, x\s9, x\c3
	eor		x\s14, x\s14, x\c3
	eor		x\s19, x\s19, x\c3
	eor		x\s24, x\s24, x\c3
	eor		x\s4, x\s4, x\c0, ror #63
	eor		x\s9, x\s9, x\c0, ror #63
	eor		x\s14, x\s14, x\c0, ror #63
	eor		x\s19, x\s19, x\c0, ror #63
	eor		x\s24, x\s24, x\c0, ror #63
	STHETA_D	SPASS
#endif
	SROL		\s4, R4
	SROL		\s9, R9
	SROL		\s14, R14
	SROL		\s19, R19
	SROL		\s24, R24
.endm
.macro SRHO_H SARGS
	SRHO1		\s0, \c4, R0
	SRHO1		\s1, \c0, R1
	SRHO1		\s2, \c1, R2
	SRHO1		\s3, \c2, R3
	SRHO1		\s5, \c4, R5
	SRHO1		\s6, \c0, R6
	SRHO1		\s7, \c1, R7
	SRHO1		\s8, \c2, R8
	SRHO1		\s10, \c4, R10
	SRHO1		\s11, \c0, R11
.endm
.macro SRHO_T SARGS
	SRHO1		\s12, \c1, R12
	SRHO1		\s13, \c2, R13
	SRHO1		\s15, \c4, R15
	SRHO1		\s16, \c0, R16
	SRHO1		\s17, \c1, R17
	SRHO1		\s18, \c2, R18
	SRHO1		\s20, \c4, R20
	SRHO1		\s21, \c0, R21
	SRHO1		\s22, \c1, R22
	SRHO1		\s23, \c2, R23
.endm

/* chi on a row: out[x] = b[x] ^ (~b[x+1] & b[x+2]) with out0..4 -> f0, f1,
 * b2, b0, b1 (b3, b4 freed). Outputs 3 and 4 are built in place: each
 * input's last use is the BIC that starts the output taking its place. */
.macro SCHI b0, b1, b2, b3, b4, f0, f1
	bic		x\f1, x\b2, x\b1
	eor		x\f0, x\b0, x\f1
	bic		x\f1, x\b3, x\b2
	eor		x\f1, x\b1, x\f1
	bic		x\b1, x\b1, x\b0
	bic		x\b0, x\b0, x\b4
	eor		x\b0, x\b3, x\b0
	eor		x\b1, x\b4, x\b1
	bic		x\b3, x\b4, x\b3
	eor		x\b2, x\b2, x\b3
.endm

/* row y of chi takes B[x] from lane ((x+3y)%5) + 5x */
.macro SCHI_ROW0 r, SARGS
	ldr		x\c0, .LRC + 16*\r
	SCHI		\s0, \s6, \s12, \s18, \s24, \c3, \c4
	eor		x\c3, x\c3, x\c0
.endm
.macro SCHI_ROW1 SARGS
	SCHI		\s3, \s9, \s10, \s16, \s22, \s18, \s24
.endm
.macro SCHI_ROW2 SARGS
	SCHI		\s1, \s7, \s13, \s19, \s20, \s16, \s22
.endm
.macro SCHI_ROW3 SARGS
	SCHI		\s4, \s5, \s11, \s17, \s23, \s19, \s20
.endm
.macro SCHI_ROW4 SARGS
	SCHI		\s2, \s8, \s14, \s15, \s21, \s17, \s23
.endm

.macro SROUND r, SARGS
	STHETA		SPASS
	SRHO		SPASS
	SCHI_ROW0	\r, SPASS
	SCHI_ROW1	SPASS
	SCHI_ROW2	SPASS
	SCHI_ROW3	SPASS
	SCHI_ROW4	SPASS
.endm

/* round 0 on lane i in x(i) (x19.. for lanes 18..24): input words in
 * x0..x7, 0x01 in x8, 0x80..0 in x16, the rest zero (not initialised: a
 * zero lane after theta and rho is just D rotated, so they get that). */
.macro SFIRST_ROUND
	eor		x26, x0, x5
	eor		x27, x1, x6
	eor		x27, x27, x16
	eor		x28, x2, x7
	eor		x29, x3, x8
	mov		x30, x4
	eor		x4, x4, x29
	eor		x4, x4, x26, ror #63
	eor		x9, x29, x26, ror #63		/* D4 */
	SROL		4, R4
	SROL2		14, 9, R14
	SROL2		20, 9, R19
	SROL2		25, 9, R24
	SROL		9, R9
	eor		x26, x26, x28, ror #63		/* D1 */
	eor		x28, x28, x30, ror #63		/* D3 */
	eor		x30, x30, x27, ror #63		/* D0 */
	eor		x27, x27, x29, ror #63		/* D2 */
	SRHO1		0, 30, R0
	SRHO1		1, 26, R1
	SRHO1		2, 27, R2
	SRHO1		3, 28, R3
	SRHO1		5, 30, R5
	SRHO1		6, 26, R6
	SRHO1		7, 27, R7
	SRHO1		8, 28, R8
	SROL2		10, 30, R10
	SROL2		11, 26, R11
	SROL2		12, 27, R12
	SROL2		13, 28, R13
	SROL2		15, 30, R15
	SRHO1		16, 26, R16
	SROL2		17, 27, R17
	SROL2		19, 28, R18
	SROL2		21, 30, R20
	SROL2		22, 26, R21
	SROL2		23, 27, R22
	SROL2		24, 28, R23
	SCHI_ROW0	0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW1	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW2	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW3	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW4	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
.endm

/* round 23: row 0, x = 0..3 only, stored at [[sp + OUT_SLOT] + OUT_OFF] */
.macro SLAST_ROUND SARGS
	STHETA_LAST	SPASS
	SRHO1		\s0, \c4, R0
	SRHO1		\s6, \c0, R6
	SRHO1		\s12, \c1, R12
	SRHO1		\s18, \c2, R18
	ldr		x\c0, .LRC + 16*23
	bic		x\c4, x\s12, x\s6
	eor		x\c3, x\s0, x\c4
	bic		x\c4, x\s18, x\s12
	eor		x\c4, x\s6, x\c4
	bic		x\s0, x\s0, x\s24
	eor		x\s0, x\s18, x\s0
	bic		x\s18, x\s24, x\s18
	eor		x\s12, x\s12, x\s18
	eor		x\c3, x\c3, x\c0
	ldr		x\c0, [sp, #OUT_SLOT]
	stp		x\c3, x\c4, [x\c0, #OUT_OFF]
	stp		x\s12, x\s0, [x\c0, #OUT_OFF + 16]
.endm

/* the node at [in] into x0..x7 (last, as in may be one of them) and the
 * padding lanes */
.macro SLOAD in
	ldp		x2, x3, [\in, #16]
	ldp		x4, x5, [\in, #32]
	ldp		x6, x7, [\in, #48]
	ldp		x0, x1, [\in]
	mov		x8, #1
	mov		x16, #0x8000000000000000
.endm
