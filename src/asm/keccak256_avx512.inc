/*
 * Keccak-f[1600] rounds for keccak256 of one 64-byte Merkle node per 64-bit
 * vector lane, shared by keccak256_avx512_x8.S (zmm, 8 nodes) and
 * keccak256_avx512vl_x4.S (ymm, 4 nodes). AVX-512F (+VL for ymm).
 *
 * The including file defines
 *   VR         the register name prefix (zmm or ymm); macro arguments are
 *              register numbers, so VR\a is zmm<a>
 *   VREG(n)    register n, n may itself be a macro (VREG(C0))
 *   VMEM(i)    vector-sized stack slot i, i = 0..9
 *   RC(r)      round constant r as an embedded broadcast operand
 *   K1, K63    0x01 and 0x80..00 (the two padding lanes) as broadcasts
 *   OUTPUT     macro taking the four digest-word registers
 *
 * State: lane i = x + 5*y of the 5x5 state. 30 of the 32 registers are
 * needed during a round (20 lanes, theta's C[0..4] and E[0..4] = rotl(C,1)),
 * so lanes 0..4 live in memory between rounds: they are the chi output of
 * row 0, written early in a round and read back only by the next round's
 * theta, which hides the store-to-load latency. The other 20 lanes and two
 * free registers move around: pi sends every lane to a new position, and
 * rather than copying registers each round takes the register list the
 * previous round left behind (the schedule at the end of KECCAK_F).
 * The two memory rows alternate between VMEM(0..4) and VMEM(5..9).
 *
 * Per round (rounds 1..22): 90 vector ops, 10 register copies, 10 loads,
 * 5 stores:
 *   theta:  C[x] = A[x,0]^..^A[x,4]                 10 vpternlogq
 *           E[x] = rotl(C[x],1)                      5 vprolq
 *   rho/pi: B = rotl(A ^ C[x-1] ^ E[x+1], r)         25 vpternlogq, 24 vprolq
 *   chi:    A' = B[x] ^ (~B[x+1] & B[x+2])           25 vpternlogq
 *   iota:   A'[0] ^= RC                              1 vpxorq (broadcast)
 *
 * Shortcuts (keccak256 of 64 bytes is a single permutation):
 *   - round 0: only lanes 0..7 hold data, lane 8 and lane 16 are padding
 *     constants, the other 15 lanes are zero (76 ops instead of 90)
 *   - round 23: only the 4 output lanes (row 0, x = 0..3) go through
 *     rho/pi/chi (29 ops)
 *
 * vpternlogq immediates: 0x96 = a^b^c, 0xD2 = a^(~b&c) (result in a).
 */

/* rho rotation offsets per lane */
#define R1  1
#define R2  62
#define R3  28
#define R4  27
#define R5  36
#define R6  44
#define R7  6
#define R8  55
#define R9  20
#define R10 3
#define R11 10
#define R12 43
#define R13 25
#define R14 39
#define R15 41
#define R16 45
#define R17 15
#define R18 21
#define R19 8
#define R20 18
#define R21 2
#define R22 61
#define R23 56
#define R24 14

/* theta's registers, fixed for all rounds; lanes use registers 0..21 */
#define C0 22
#define C1 23
#define C2 24
#define C3 25
#define C4 26
#define E0 27
#define E1 28
#define E2 29
#define E3 30
#define E4 31

/* memory row of round r: lanes 0..4 are read from row r&1 and the new
 * lanes 0..4 written to row (r+1)&1 */
#define LIN(r, x)	VMEM(5*((r)&1) + (x))
#define LOUT(r, x)	VMEM(5*(((r)+1)&1) + (x))

/* B = rotl(A ^ C[x-1] ^ E[x+1], rot), in place */
.macro THETA_RHO a, cm1, ep1, rot
	vpternlogq	VR\a, VR\cm1, VR\ep1, 0x96
.if \rot
	vprolq		VR\a, VR\a, \rot
.endif
.endm

/* chi over one row b0..b4. b_x can take its own output once the later
 * outputs no longer need it: true for x = 2, 3, 4. Outputs x = 0, 1 go to
 * the free registers t0, t1; b0, b1 are free afterwards. */
.macro CHI_ROW b0, b1, b2, b3, b4, t0, t1
	vmovdqa64	VR\t0, VR\b0
	vpternlogq	VR\t0, VR\b1, VR\b2, 0xD2
	vmovdqa64	VR\t1, VR\b1
	vpternlogq	VR\t1, VR\b2, VR\b3, 0xD2
	vpternlogq	VR\b2, VR\b3, VR\b4, 0xD2
	vpternlogq	VR\b3, VR\b4, VR\b0, 0xD2
	vpternlogq	VR\b4, VR\b0, VR\b1, 0xD2
.endm

/* chi over row 0, with iota, straight to memory row LOUT(r); t is free */
.macro CHI_ROW0 r, b0, b1, b2, b3, b4, t
	vmovdqa64	VR\t, VR\b0
	vpternlogq	VR\t, VR\b1, VR\b2, 0xD2
	vpxorq		VR\t, VR\t, RC(\r)
	vmovdqa64	LOUT(\r, 0), VR\t
	vmovdqa64	VR\t, VR\b1
	vpternlogq	VR\t, VR\b2, VR\b3, 0xD2
	vmovdqa64	LOUT(\r, 1), VR\t
	vpternlogq	VR\b2, VR\b3, VR\b4, 0xD2
	vmovdqa64	LOUT(\r, 2), VR\b2
	vpternlogq	VR\b3, VR\b4, VR\b0, 0xD2
	vmovdqa64	LOUT(\r, 3), VR\b3
	vpternlogq	VR\b4, VR\b0, VR\b1, 0xD2
	vmovdqa64	LOUT(\r, 4), VR\b4
.endm

/* theta step 1: C[x] = lane x (memory) ^ the four lanes x+5..x+20,
 * E[x] = rotl(C[x], 1) */
.macro THETA r, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, \
		a15, a16, a17, a18, a19, a20, a21, a22, a23, a24
	vmovdqa64	VREG(C0), LIN(\r, 0)
	vpternlogq	VREG(C0), VR\a5, VR\a10, 0x96
	vpternlogq	VREG(C0), VR\a15, VR\a20, 0x96
	vmovdqa64	VREG(C1), LIN(\r, 1)
	vpternlogq	VREG(C1), VR\a6, VR\a11, 0x96
	vpternlogq	VREG(C1), VR\a16, VR\a21, 0x96
	vmovdqa64	VREG(C2), LIN(\r, 2)
	vpternlogq	VREG(C2), VR\a7, VR\a12, 0x96
	vpternlogq	VREG(C2), VR\a17, VR\a22, 0x96
	vmovdqa64	VREG(C3), LIN(\r, 3)
	vpternlogq	VREG(C3), VR\a8, VR\a13, 0x96
	vpternlogq	VREG(C3), VR\a18, VR\a23, 0x96
	vmovdqa64	VREG(C4), LIN(\r, 4)
	vpternlogq	VREG(C4), VR\a9, VR\a14, 0x96
	vpternlogq	VREG(C4), VR\a19, VR\a24, 0x96
	vprolq		VREG(E0), VREG(C0), 1
	vprolq		VREG(E1), VREG(C1), 1
	vprolq		VREG(E2), VREG(C2), 1
	vprolq		VREG(E3), VREG(C3), 1
	vprolq		VREG(E4), VREG(C4), 1
.endm

/*
 * One full round. a5..a24: lane registers, t0/t1: the two free registers,
 * r: round index. Row y gathers B[x] from lane ((x+3y)%5) + 5x (pi), one of
 * which is a memory lane (0..4), loaded into a register freed by the row
 * before. Row 0 goes to memory, rows 1..4 into the registers below, so the
 * next round finds
 *   lanes 5..9   in t0,  t1,  a10, a16, a22
 *   lanes 10..14 in a18, a24, a13, a19, a20
 *   lanes 15..19 in a9,  a12, a11, a17, a23
 *   lanes 20..24 in a6,  a5,  a14, a15, a21     free: a7, a8
 */
.macro ROUND r, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, \
		a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, t0, t1
	THETA	\r, \a5, \a6, \a7, \a8, \a9, \a10, \a11, \a12, \a13, \a14, \
		\a15, \a16, \a17, \a18, \a19, \a20, \a21, \a22, \a23, \a24
	/* row 0: lanes 0, 6, 12, 18, 24 -> memory */
	vmovdqa64	VR\t0, LIN(\r, 0)
	THETA_RHO	\t0,  C4, E1, 0
	THETA_RHO	\a6,  C0, E2, R6
	THETA_RHO	\a12, C1, E3, R12
	THETA_RHO	\a18, C2, E4, R18
	THETA_RHO	\a24, C3, E0, R24
	CHI_ROW0	\r, \t0, \a6, \a12, \a18, \a24, \t1
	/* row 1: lanes 3, 9, 10, 16, 22 -> t0, t1, a10, a16, a22 */
	vmovdqa64	VR\a6, LIN(\r, 3)
	THETA_RHO	\a6,  C2, E4, R3
	THETA_RHO	\a9,  C3, E0, R9
	THETA_RHO	\a10, C4, E1, R10
	THETA_RHO	\a16, C0, E2, R16
	THETA_RHO	\a22, C1, E3, R22
	CHI_ROW		\a6, \a9, \a10, \a16, \a22, \t0, \t1
	/* row 2: lanes 1, 7, 13, 19, 20 -> a18, a24, a13, a19, a20 */
	vmovdqa64	VR\a12, LIN(\r, 1)
	THETA_RHO	\a12, C0, E2, R1
	THETA_RHO	\a7,  C1, E3, R7
	THETA_RHO	\a13, C2, E4, R13
	THETA_RHO	\a19, C3, E0, R19
	THETA_RHO	\a20, C4, E1, R20
	CHI_ROW		\a12, \a7, \a13, \a19, \a20, \a18, \a24
	/* row 3: lanes 4, 5, 11, 17, 23 -> a9, a12, a11, a17, a23 */
	vmovdqa64	VR\a6, LIN(\r, 4)
	THETA_RHO	\a6,  C3, E0, R4
	THETA_RHO	\a5,  C4, E1, R5
	THETA_RHO	\a11, C0, E2, R11
	THETA_RHO	\a17, C1, E3, R17
	THETA_RHO	\a23, C2, E4, R23
	CHI_ROW		\a6, \a5, \a11, \a17, \a23, \a9, \a12
	/* row 4: lanes 2, 8, 14, 15, 21 -> a6, a5, a14, a15, a21 */
	vmovdqa64	VR\a7, LIN(\r, 2)
	THETA_RHO	\a7,  C1, E3, R2
	THETA_RHO	\a8,  C2, E4, R8
	THETA_RHO	\a14, C3, E0, R14
	THETA_RHO	\a15, C4, E1, R15
	THETA_RHO	\a21, C0, E2, R21
	CHI_ROW		\a7, \a8, \a14, \a15, \a21, \a6, \a5
.endm

/* Round 23: theta, then row 0 only, x = 0..3. The digest words end up in
 * t0, t1, a12, a18 and go to OUTPUT. */
.macro LAST_ROUND a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, \
		a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, t0, t1
	THETA	23, \a5, \a6, \a7, \a8, \a9, \a10, \a11, \a12, \a13, \a14, \
		\a15, \a16, \a17, \a18, \a19, \a20, \a21, \a22, \a23, \a24
	vmovdqa64	VR\t0, LIN(23, 0)
	THETA_RHO	\t0,  C4, E1, 0
	THETA_RHO	\a6,  C0, E2, R6
	THETA_RHO	\a12, C1, E3, R12
	THETA_RHO	\a18, C2, E4, R18
	THETA_RHO	\a24, C3, E0, R24
	vmovdqa64	VR\t1, VR\t0
	vpternlogq	VR\t1, VR\a6, VR\a12, 0xD2
	vpxorq		VR\t1, VR\t1, RC(23)
	vpternlogq	VR\a6, VR\a12, VR\a18, 0xD2
	vpternlogq	VR\a12, VR\a18, VR\a24, 0xD2
	vpternlogq	VR\a18, VR\a24, VR\t0, 0xD2
	OUTPUT		\t1, \a6, \a12, \a18
.endm

/* round 0 helpers: B = rotl(A ^ D, rot) in place, and B = rotl(D, rot)
 * into a free register for a lane that is still zero */
.macro THETA_RHO0 a, d, rot
	vpxorq		VR\a, VR\a, VR\d
.if \rot
	vprolq		VR\a, VR\a, \rot
.endif
.endm
.macro RHO0 b, d, rot
	vprolq		VR\b, VR\d, \rot
.endm

/*
 * The whole permutation. Expects word j of every node in register j
 * (j = 0..7); registers 8..31 are free.
 *
 * Round 0: only lanes 0..7, 8 (= 0x01) and 16 (= 0x80..00) are non-zero, so
 * theta computes D[x] = C[x-1] ^ rotl(C[x+1],1) once per column (in the E
 * registers) and a zero lane's B is just rotl(D, r), written to any free
 * register.
 */
.macro KECCAK_F
	vpxorq		VREG(C0), VREG(0), VREG(5)
	vpxorq		VREG(C1), VREG(1), VREG(6)
	vpxorq		VREG(C1), VREG(C1), K63
	vpxorq		VREG(C2), VREG(2), VREG(7)
	vpxorq		VREG(C3), VREG(3), K1		/* C4 is lane 4 itself */
	vprolq		VREG(E0), VREG(C1), 1
	vpxorq		VREG(E0), VREG(E0), VREG(4)	/* D0 = C4 ^ rotl(C1) */
	vprolq		VREG(E1), VREG(C2), 1
	vpxorq		VREG(E1), VREG(E1), VREG(C0)	/* D1 = C0 ^ rotl(C2) */
	vprolq		VREG(E2), VREG(C3), 1
	vpxorq		VREG(E2), VREG(E2), VREG(C1)	/* D2 = C1 ^ rotl(C3) */
	vprolq		VREG(E3), VREG(4), 1
	vpxorq		VREG(E3), VREG(E3), VREG(C2)	/* D3 = C2 ^ rotl(C4) */
	vprolq		VREG(E4), VREG(C0), 1
	vpxorq		VREG(E4), VREG(E4), VREG(C3)	/* D4 = C3 ^ rotl(C0) */
	/* row 0: lanes 0, 6, 12, 18, 24 -> memory */
	THETA_RHO0	0,  E0, 0
	THETA_RHO0	6,  E1, R6
	RHO0		8,  E2, R12
	RHO0		9,  E3, R18
	RHO0		10, E4, R24
	CHI_ROW0	0, 0, 6, 8, 9, 10, 11
	/* row 1: lanes 3, 9, 10, 16, 22 */
	THETA_RHO0	3,  E3, R3
	RHO0		0,  E4, R9
	RHO0		6,  E0, R10
	vpxorq		VREG(8), VREG(E1), K63		/* padding lane 16: */
	vprolq		VREG(8), VREG(8), R16		/* rotl(K ^ D, r) */
	RHO0		9,  E2, R22
	CHI_ROW		3, 0, 6, 8, 9, 10, 11
	/* row 2: lanes 1, 7, 13, 19, 20 */
	THETA_RHO0	1,  E1, R1
	THETA_RHO0	7,  E2, R7
	RHO0		12, E3, R13
	RHO0		13, E4, R19
	RHO0		14, E0, R20
	CHI_ROW		1, 7, 12, 13, 14, 3, 0
	/* row 3: lanes 4, 5, 11, 17, 23 */
	THETA_RHO0	4,  E4, R4
	THETA_RHO0	5,  E0, R5
	RHO0		15, E1, R11
	RHO0		16, E2, R17
	RHO0		17, E3, R23
	CHI_ROW		4, 5, 15, 16, 17, 1, 7
	/* row 4: lanes 2, 8, 14, 15, 21 */
	THETA_RHO0	2,  E2, R2
	vpxorq		VREG(18), VREG(E3), K1		/* padding lane 8 */
	vprolq		VREG(18), VREG(18), R8
	RHO0		19, E4, R14
	RHO0		20, E0, R15
	RHO0		21, E1, R21
	CHI_ROW		2, 18, 19, 20, 21, 4, 5

	/* rounds 1..23: each line is the previous round's placement of lanes
	 * 5..24, then the two free registers (see ROUND) */
	ROUND	1, 10, 11, 6, 8, 9, 3, 0, 12, 13, 14, 1, 7, 15, 16, 17, 4, 5, 19, 20, 21, 2, 18
	ROUND	2, 2, 18, 3, 7, 19, 16, 21, 13, 17, 4, 9, 12, 0, 15, 20, 11, 10, 14, 1, 5, 6, 8
	ROUND	3, 6, 8, 16, 12, 14, 15, 5, 17, 20, 11, 19, 13, 21, 0, 1, 18, 2, 4, 9, 10, 3, 7
	ROUND	4, 3, 7, 15, 13, 4, 0, 10, 20, 1, 18, 14, 17, 5, 21, 9, 8, 6, 11, 19, 2, 16, 12
	ROUND	5, 16, 12, 0, 17, 11, 21, 2, 1, 9, 8, 4, 20, 10, 5, 19, 7, 3, 18, 14, 6, 15, 13
	ROUND	6, 15, 13, 21, 20, 18, 5, 6, 9, 19, 7, 11, 1, 2, 10, 14, 12, 16, 8, 4, 3, 0, 17
	ROUND	7, 0, 17, 5, 1, 8, 10, 3, 19, 14, 12, 18, 9, 6, 2, 4, 13, 15, 7, 11, 16, 21, 20
	ROUND	8, 21, 20, 10, 9, 7, 2, 16, 14, 4, 13, 8, 19, 3, 6, 11, 17, 0, 12, 18, 15, 5, 1
	ROUND	9, 5, 1, 2, 19, 12, 6, 15, 4, 11, 17, 7, 14, 16, 3, 18, 20, 21, 13, 8, 0, 10, 9
	ROUND	10, 10, 9, 6, 14, 13, 3, 0, 11, 18, 20, 12, 4, 15, 16, 8, 1, 5, 17, 7, 21, 2, 19
	ROUND	11, 2, 19, 3, 4, 17, 16, 21, 18, 8, 1, 13, 11, 0, 15, 7, 9, 10, 20, 12, 5, 6, 14
	ROUND	12, 6, 14, 16, 11, 20, 15, 5, 8, 7, 9, 17, 18, 21, 0, 12, 19, 2, 1, 13, 10, 3, 4
	ROUND	13, 3, 4, 15, 18, 1, 0, 10, 7, 12, 19, 20, 8, 5, 21, 13, 14, 6, 9, 17, 2, 16, 11
	ROUND	14, 16, 11, 0, 8, 9, 21, 2, 12, 13, 14, 1, 7, 10, 5, 17, 4, 3, 19, 20, 6, 15, 18
	ROUND	15, 15, 18, 21, 7, 19, 5, 6, 13, 17, 4, 9, 12, 2, 10, 20, 11, 16, 14, 1, 3, 0, 8
	ROUND	16, 0, 8, 5, 12, 14, 10, 3, 17, 20, 11, 19, 13, 6, 2, 1, 18, 15, 4, 9, 16, 21, 7
	ROUND	17, 21, 7, 10, 13, 4, 2, 16, 20, 1, 18, 14, 17, 3, 6, 9, 8, 0, 11, 19, 15, 5, 12
	ROUND	18, 5, 12, 2, 17, 11, 6, 15, 1, 9, 8, 4, 20, 16, 3, 19, 7, 21, 18, 14, 0, 10, 13
	ROUND	19, 10, 13, 6, 20, 18, 3, 0, 9, 19, 7, 11, 1, 15, 16, 14, 12, 5, 8, 4, 21, 2, 17
	ROUND	20, 2, 17, 3, 1, 8, 16, 21, 19, 14, 12, 18, 9, 0, 15, 4, 13, 10, 7, 11, 5, 6, 20
	ROUND	21, 6, 20, 16, 9, 7, 15, 5, 14, 4, 13, 8, 19, 21, 0, 11, 17, 2, 12, 18, 10, 3, 1
	ROUND	22, 3, 1, 15, 19, 12, 0, 10, 4, 11, 17, 7, 14, 5, 21, 18, 20, 6, 13, 8, 2, 16, 9
	LAST_ROUND 16, 9, 0, 14, 13, 21, 2, 11, 18, 20, 12, 4, 10, 5, 8, 1, 3, 17, 7, 6, 15, 19
.endm
