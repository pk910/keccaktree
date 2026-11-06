/*
 * keccak-f[1600] rounds on 2 nodes with lane pairs: node j of a batch in
 * the 128-bit half j of every ymm register, and two lanes of its state in
 * the two qwords of that half. Used by keccak256_avx2_x2.S.
 *
 * Why: keccak256_avx2.inc puts one node in each qword, so a batch of 4 is
 * the unit of work and 2 nodes cost as much as 4. With two lanes of a node
 * per half, 2 nodes take 13 registers (5 rows x (lanes 0,1 | 2,3) and the
 * column-4 lanes as rows (0,1), (2,3), (4)), and the lane shuffles that
 * theta, pi and chi need stay inside the 128-bit halves (vshufpd,
 * vpermilpd, vmovddup: 1 cycle, no vpermq). About 147 vector operations
 * per round for 2 nodes, against 183 for a padded batch of 4.
 *
 * The state lives in two 15-slot buffers in memory (as in the x4 kernel):
 * chi reads all 13 state registers to write 13, which do not fit next to
 * them. Each round:
 *   theta:  D01 = (C4,C0) ^ rotl((C1,C2), 1), D23 = (C1,C2) ^
 *           rotl((C3,C4), 1), D4 = C3 ^ rotl(C0, 1) broadcast     18 ops
 *   rho:    R = rotl(slot ^ D, r) per lane (vpsllvq/vpsrlvq/vpor)  54 ops
 *   chi:    per row 6 vshufpd gather the B pairs (pi), 3 vpandn,
 *           3 vpxor, 3 stores                                    60 ops
 *   iota                                                           1 op
 *   parity: C01, C23, C4 accumulated from the chi outputs         14 ops
 * Slot k of a buffer: 2y = row y lanes (0,1), 2y+1 = row y lanes (2,3),
 * 10+y = row y lane 4 in qword 0 (qword 1 is unspecified).
 *
 * Every round waits for the parities of the one before, so their chain
 * must not go through memory: chi runs the rows in the order 0, 2, 4, 1,
 * 3, after which the registers of R0_01 and R2_23 (read by rows 0 and 2
 * only) and R1_23 (rows 2 and 4) are free to accumulate C01, C23 and C4;
 * rows 0 and 2 contribute from their stored slots. Even so a round is
 * bound by its dependency chain (parity, theta, rho, chi: 11 operations
 * deep) plus the chi work that cannot overlap it, about 55 cycles on
 * Zen 3 against 58 for the x4 round, which is why 2 nodes here cost only
 * 8% less than a padded batch of 4 there (27% less on an Alder Lake
 * E-core, whose halves of a ymm operation run on separate ports).
 *
 * Registers: ymm0..12 the state after rho (R<y>_01, R<y>_23, Q01, Q23,
 * Q4), ymm13..15 D01, D23, D4 then temporaries.
 */
#define SLOT(b, k)	ymmword ptr [b + 32*(k)]

#define R0_01	ymm0
#define R0_23	ymm1
#define R1_01	ymm2
#define R1_23	ymm3
#define R2_01	ymm4
#define R2_23	ymm5
#define R3_01	ymm6
#define R3_23	ymm7
#define R4_01	ymm8
#define R4_23	ymm9
#define Q01	ymm10
#define Q23	ymm11
#define Q4	ymm12
#define D01	ymm13
#define D23	ymm14
#define D4	ymm15
#define T0	ymm13
#define T1	ymm14
#define T2	ymm15
/* parities (free state registers) and theta temporaries */
#define C01	ymm0
#define C23	ymm5
#define C4	ymm3
#define U0	ymm1
#define U1	ymm2
#define U2	ymm4

/* d = (a.q[qa], b.q[qb]) in each half */
.macro PAIR d, a, qa, b, qb
	vshufpd		\d, \a, \b, 5*\qa + 10*\qb
.endm

/* d = rotl(s, 1); t is scratch */
.macro ROL1 d, s, t
	vpsrlq		\t, \s, 63
	vpaddq		\d, \s, \s
	vpor		\d, \d, \t
.endm

/* D01, D23, D4 from the parities C01, C23, C4 (qword 0 of C4) */
.macro THETA
	PAIR		U1, C01, 1, C23, 0		/* (C1, C2) */
	PAIR		U0, C23, 1, C4, 0		/* (C3, C4) */
	ROL1		D23, U0, U2
	ROL1		D01, U1, U0
	vpxor		D23, D23, U1
	PAIR		U1, C4, 0, C01, 0		/* (C4, C0) */
	ROL1		D4, C01, U2			/* (rotl C0, rotl C1) */
	vpxor		D01, D01, U1
	vpermilpd	U0, C23, 0b0101			/* (C3, C2) */
	vpxor		D4, D4, U0
	vmovddup	D4, D4				/* (D4, D4) */
.endm

/* r = rotl(r, by the lane pair's offsets at k) */
.macro RHO r, k, t
	vpsllvq		\t, \r, ymmword ptr [rip + .LROTL + 32*\k]
	vpsrlvq		\r, \r, ymmword ptr [rip + .LROTR + 32*\k]
	vpor		\r, \r, \t
.endm

/* the state at in, with theta applied and rotated, into ymm0..12 */
.macro THETA_RHO in
	vpxor		R0_01, D01, SLOT(\in, 0)
	vpxor		R0_23, D23, SLOT(\in, 1)
	vpxor		R2_01, D01, SLOT(\in, 4)
	vpxor		R2_23, D23, SLOT(\in, 5)
	vpxor		R4_01, D01, SLOT(\in, 8)
	vpxor		R4_23, D23, SLOT(\in, 9)
	vpxor		R1_01, D01, SLOT(\in, 2)
	vpxor		R1_23, D23, SLOT(\in, 3)
	vmovdqa		Q01, SLOT(\in, 10)
	vmovdqa		Q23, SLOT(\in, 12)
	vshufpd		Q01, Q01, SLOT(\in, 11), 0	/* (A40, A41) */
	vpxor		Q4, D4, SLOT(\in, 14)
	vpxor		Q01, Q01, D4
	vpxor		R3_01, D01, SLOT(\in, 6)
	vpxor		R3_23, D23, SLOT(\in, 7)
	vshufpd		Q23, Q23, SLOT(\in, 13), 0	/* (A42, A43) */
	vpxor		Q23, Q23, D4
	RHO		R0_01, 0, T0
	RHO		R0_23, 1, T1
	RHO		R2_01, 4, T2
	RHO		R2_23, 5, T0
	RHO		R4_01, 8, T1
	RHO		R4_23, 9, T2
	RHO		R1_01, 2, T0
	RHO		R1_23, 3, T1
	RHO		Q01, 10, T2
	RHO		Q4, 12, T0
	RHO		R3_01, 6, T1
	RHO		R3_23, 7, T2
	RHO		Q23, 11, T0
.endm

/* chi on row y: B[x] = (register bx, qword qx); out[x] = B[x] ^ (~B[x+1] &
 * B[x+2]) stored as (out0, out1), (out2, out3) and (out4, -) to the row's
 * slots at out. P<ab> is the pair (B[a], B[b]). Row 0 takes iota. The
 * outputs also go to the parities once their registers are free (acc:
 * rows 4, 1, 3; row 4 starts C4 with the stored lane-4 outputs of rows 0
 * and 2, row 2 starts C01 and C23 from its and row 0's slots). */
.macro CHI_ROW out, y, rc, b0, q0, b1, q1, b2, q2, b3, q3, b4, q4, acc
	PAIR		T0, \b1, \q1, \b2, \q2		/* P12 */
	PAIR		T1, \b2, \q2, \b3, \q3		/* P23 */
	vpandn		T2, T0, T1
	PAIR		T1, \b0, \q0, \b1, \q1		/* P01 */
	vpxor		T2, T2, T1
.if \y == 0
	vpxor		T2, T2, ymmword ptr [RCP + \rc]
.endif
	vmovdqa		SLOT(\out, 2*\y), T2
.if \acc
	vpxor		C01, C01, T2
.endif
	vpandn		T2, T1, T0
	PAIR		T0, \b4, \q4, \b0, \q0		/* P40 */
	vpxor		T2, T2, T0
	vmovdqa		SLOT(\out, 10 + \y), T2
.if \y == 4
	vpxor		C4, T2, SLOT(\out, 10)
	vpxor		C4, C4, SLOT(\out, 12)
.elseif \acc
	vpxor		C4, C4, T2
.endif
	PAIR		T1, \b3, \q3, \b4, \q4		/* P34 */
	vpandn		T2, T1, T0
	PAIR		T1, \b2, \q2, \b3, \q3		/* P23 */
	vpxor		T2, T2, T1
	vmovdqa		SLOT(\out, 2*\y + 1), T2
.if \acc
	vpxor		C23, C23, T2
.endif
.if \y == 2
	vmovdqa		C01, SLOT(\out, 4)
	vmovdqa		C23, SLOT(\out, 5)
	vpxor		C01, C01, SLOT(\out, 0)
	vpxor		C23, C23, SLOT(\out, 1)
.endif
.endm

/* row y of chi takes B[x] from lane ((x+3y)%5) + 5x: column (x+3y)%5 of
 * row x; rows in the order that frees the parity registers */
.macro CHI out, rc
	CHI_ROW		\out, 0, \rc, R0_01, 0, R1_01, 1, R2_23, 0, R3_23, 1, Q4, 0, 0
	CHI_ROW		\out, 2, \rc, R0_01, 1, R1_23, 0, R2_23, 1, Q23, 1, R4_01, 0, 0
	CHI_ROW		\out, 4, \rc, R0_23, 0, R1_23, 1, Q23, 0, R3_01, 0, R4_01, 1, 1
	CHI_ROW		\out, 1, \rc, R0_23, 1, Q01, 1, R2_01, 0, R3_01, 1, R4_23, 0, 1
	CHI_ROW		\out, 3, \rc, Q01, 0, R1_01, 0, R2_01, 1, R3_23, 0, R4_23, 1, 1
.endm

/* one round from the state at in to out, iota constant at [RCP + rc];
 * parities in C01, C23, C4 on entry and exit */
.macro ROUND in, out, rc
	THETA
	THETA_RHO	\in
	CHI		\out, \rc
.endm

/* the two nodes at in into the state slots at s: lanes 0..7 data, 8 = 0x01,
 * 16 = 0x80..00, rest zero */
.macro LOAD in, s
	vmovdqu		xmm0, xmmword ptr [\in + 0]
	vmovdqu		xmm1, xmmword ptr [\in + 16]
	vmovdqu		xmm2, xmmword ptr [\in + 32]
	vmovdqu		xmm3, xmmword ptr [\in + 48]
	vinserti128	ymm0, ymm0, xmmword ptr [\in + 64], 1	/* (w0, w1) */
	vinserti128	ymm1, ymm1, xmmword ptr [\in + 80], 1	/* (w2, w3) */
	vinserti128	ymm2, ymm2, xmmword ptr [\in + 96], 1	/* (w4, w5) */
	vinserti128	ymm3, ymm3, xmmword ptr [\in + 112], 1	/* (w6, w7) */
	vpxor		ymm4, ymm4, ymm4
	vmovdqa		ymm5, ymmword ptr [rip + .LK1]
	vmovdqa		ymm6, ymmword ptr [rip + .LK63]
	PAIR		ymm7, ymm2, 1, ymm3, 0			/* (w5, w6) */
	PAIR		ymm3, ymm3, 1, ymm5, 0			/* (w7, 1) */
	vmovdqa		SLOT(\s, 0), ymm0
	vmovdqa		SLOT(\s, 1), ymm1
	vmovdqa		SLOT(\s, 10), ymm2			/* (w4, -) */
	vmovdqa		SLOT(\s, 2), ymm7
	vmovdqa		SLOT(\s, 3), ymm3
	vmovdqa		SLOT(\s, 11), ymm4
	vmovdqa		SLOT(\s, 4), ymm4
	vmovdqa		SLOT(\s, 5), ymm4
	vmovdqa		SLOT(\s, 12), ymm4
	vmovdqa		SLOT(\s, 6), ymm6			/* (0, 1<<63) */
	vmovdqa		SLOT(\s, 7), ymm4
	vmovdqa		SLOT(\s, 13), ymm4
	vmovdqa		SLOT(\s, 8), ymm4
	vmovdqa		SLOT(\s, 9), ymm4
	vmovdqa		SLOT(\s, 14), ymm4
	vpxor		C23, ymm1, ymm3			/* parities of this state */
	vpxor		C01, ymm0, ymm7
	vpxor		C01, C01, ymm6
	vmovdqa		C4, ymm2
.endm

/* digests from the state at s to out */
.macro OUTPUT s, out
	vmovdqa		ymm0, SLOT(\s, 0)
	vmovdqa		ymm1, SLOT(\s, 1)
	vmovdqu		xmmword ptr [\out + 0], xmm0
	vmovdqu		xmmword ptr [\out + 16], xmm1
	vextracti128	xmmword ptr [\out + 32], ymm0, 1
	vextracti128	xmmword ptr [\out + 48], ymm1, 1
.endm

/* constants: round constants in lane 0 of each half, padding words, and
 * the rotation offsets of each slot's lane pair (left, and 64 - left) */
.macro PAIR_RODATA
#ifdef _WIN64
.section .rdata,"dr"
#else
.section .rodata
#endif
.p2align 5
.LRC2:
	.irp rc, 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000, \
		 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009, \
		 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a, \
		 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003, \
		 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a, \
		 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
	.quad \rc, 0, \rc, 0
	.endr
.LK1:	.quad 1, 1, 1, 1
.LK63:	.quad 0, 0x8000000000000000, 0, 0x8000000000000000
/* slot k: lanes (5y, 5y+1), (5y+2, 5y+3), then (4, 9), (14, 19), (24, 24) */
.LROTL:
	.quad 0, 1, 0, 1
	.quad 62, 28, 62, 28
	.quad 36, 44, 36, 44
	.quad 6, 55, 6, 55
	.quad 3, 10, 3, 10
	.quad 43, 25, 43, 25
	.quad 41, 45, 41, 45
	.quad 15, 21, 15, 21
	.quad 18, 2, 18, 2
	.quad 61, 56, 61, 56
	.quad 27, 20, 27, 20
	.quad 39, 8, 39, 8
	.quad 14, 14, 14, 14
.LROTR:
	.quad 64, 63, 64, 63
	.quad 2, 36, 2, 36
	.quad 28, 20, 28, 20
	.quad 58, 9, 58, 9
	.quad 61, 54, 61, 54
	.quad 21, 39, 21, 39
	.quad 23, 19, 23, 19
	.quad 49, 43, 49, 43
	.quad 46, 62, 46, 62
	.quad 3, 8, 3, 8
	.quad 37, 44, 37, 44
	.quad 25, 56, 25, 56
	.quad 50, 50, 50, 50
.endm
