/*
 * Keccak-f[1600] rounds for keccak256 of one 64-byte Merkle node per 64-bit
 * vector lane with every lane in a register: the "D-form" rounds, shared by
 * keccak256_avx512_x8d.S (zmm, 8 nodes), keccak256_avx512_x9d.S (the same
 * plus a scalar node) and keccak256_avx512vl_x4d.S (ymm, 4 nodes).
 * AVX-512F (+VL for ymm). The including file defines the same names as for
 * keccak256_avx512.inc (VR, VREG, RC, RCL, RCP, LOOP_CNT, K1, K63, ROT8,
 * ROT56, OUTPUT, and optionally VHOOK / RHOOK_BEGIN / RHOOK_END).
 *
 * keccak256_avx512.inc keeps theta's column sums C[0..4] and E[0..4] =
 * rotl(C, 1) in ten registers and folds both into each lane with one
 * vpternlogq (A ^ C[x-1] ^ E[x+1]), which leaves room for 20 lanes: five
 * live in memory (5 stores and 10 loads per round) and the round has 60
 * ternlogs. Here theta forms D[x] = C[x-1] ^ rotl(C[x+1], 1) once per
 * column (5 rotations, 5 more xors) and applies it with a plain xor, so
 * theta needs five registers and all 25 lanes stay in registers: 25 lanes
 * + 5 D + 2 chi temporaries = 32.
 *
 * Per round: 95 vector ALU ops, 15 register copies, no memory access
 * (110 macro-ops against 115):
 *   theta:  C[x] = A[x,0]^..^A[x,4]              5 copies, 10 vpternlogq
 *           D[x] = C[x-1] ^ rotl(C[x+1], 1)      5 vprolq, 5 vpxorq
 *           A ^= D[x]                            25 vpxorq
 *   rho/pi: B = rotl(A, r)                       24 rotations
 *   chi:    A' = B[x] ^ (~B[x+1] & B[x+2])       10 copies, 25 vpternlogq
 *   iota:   A'[0] ^= RC                          1 vpxorq (broadcast)
 *
 * Why it is faster on AMD (measured on the GitHub runners, min of 9
 * interleaved rounds against keccak256_avx512.inc): a vpternlogq zmm whose
 * second or third source was written by a recent instruction runs at one
 * per cycle on Zen 4 (0.6 cycles with stale sources, 0.5 for vpxorq), with
 * a latency of 2 through those operands, and the ymm form at half its
 * independent throughput; the old round has 60 such ternlogs, this one 35,
 * and the 25 xors that replace them cost nothing extra. Zen 5 is bound by
 * the macro-ops it renames (avx512_x8 and avx512vl_x4 take the same time
 * per round there), and this round has 5 fewer. Ice Lake, bound by its
 * two 512-bit ALU ports, loses 6.5% to the 5 extra ALU ops, so these
 * rounds are separate kernels and keccaktree_detect times them against the
 * old ones:
 *   Zen 4 (EPYC 9V74): avx512_x8d 1.12x avx512_x8, avx512_x9d 1.166x
 *     avx512_x9 (43.4 ns/node), avx512vl_x4d 1.18x avx512vl_x4
 *   Zen 5 (EPYC 9V45): avx512_x8d 1.19x (20.9 ns/node), avx512vl_x4d 1.17x
 *   Emerald Rapids (8573C) 1.035x, Granite Rapids (6973P) 1.006x,
 *   Ice Lake (8370C) 0.935x: not picked there.
 * Variants measured and dropped (notes/zen4.md of the optimization
 * project): the chi outputs as vpandnq + vpxorq (Zen 4 1.04x / 0.97x,
 * Ice Lake 0.87x / 0.77x), rho of all lanes before any chi (1.05x), the
 * column sums as xor chains (1.10x, Zen 5 1.18x) or xor-ternlog-xor
 * (1.11x, Zen 5 1.21x; +5 ALU ops for Intel), fully unrolled (same speed
 * as the four-round loop).
 *
 * Registers move as in keccak256_avx512.inc: each round is written for the
 * register list the previous round left behind. ROUND_D takes the 25 lane
 * registers l0..l24 (lane i = x + 5y in l_i) and seven free registers
 * f0..f6: the column sums go to f0..f4 and D[0..4] end up in f5, f6, f3,
 * f4, f0, leaving f1, f2 as the chi temporaries of row 0. Chi row y writes
 * its outputs x = 0, 1 to the two temporaries and x = 2, 3, 4 in place; the
 * registers of its inputs x = 0, 1 are the temporaries of the next row, and
 * those of row 4 plus the five D registers are the free registers of the
 * next round. The round lists below follow from that (a script in the
 * notes prints them); the loop body's four rounds end 25 copies away from
 * their entry placement.
 *
 * Shortcuts (keccak256 of 64 bytes is a single permutation):
 *   - round 0: only lanes 0..7 hold data, lane 8 and lane 16 are padding
 *     constants, the other 15 lanes are zero: B = rotl(D, r) for them
 *   - round 23: only the 4 output lanes (row 0, x = 0..3) go through
 *     rho/pi/chi
 *
 * vpternlogq immediates: 0x96 = a^b^c, 0xD2 = a^(~b&c) (result in a).
 *
 * The lane macros end with VHOOK (argument: t for a theta step, r for a
 * rho lane, c for a chi lane), empty here; a kernel that interleaves other
 * work into the rounds (keccak256_avx512_x9d.S) defines it first; the
 * round macros bracket every round with RHOOK_BEGIN k / RHOOK_END, empty
 * here, for the same purpose.
 */
#ifndef VHOOK_DEFINED
.macro VHOOK kind
.endm
#endif
#ifndef RHOOK_DEFINED
.macro RHOOK_BEGIN k
.endm
.macro RHOOK_END
.endm
#endif

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

/* iota's constant: RC(r) (rip-relative, by round) or, inside the loop
 * body of KECCAK_F_D_LOOP, RCL(k) (relative to the RCP register) */
.set LOOP_RC, 0

/* theta: C[x] = l_x ^ l_x+5 ^ .. ^ l_x+20 in c0..c4 (the five copies, then
 * the first and the second ternlog of every column, so that no ternlog
 * waits on the one before it), then D[0..4] = C[x-1] ^ rotl(C[x+1], 1) in
 * t0, t1, c3, c4, c0; c1 and c2 are free afterwards */
.macro THETA_D l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, \
		l15, l16, l17, l18, l19, l20, l21, l22, l23, l24, c0, c1, c2, c3, c4, t0, t1
	vmovdqa64	VR\c0, VR\l0
	vmovdqa64	VR\c1, VR\l1
	vmovdqa64	VR\c2, VR\l2
	vmovdqa64	VR\c3, VR\l3
	vmovdqa64	VR\c4, VR\l4
	vpternlogq	VR\c0, VR\l5, VR\l10, 0x96
	vpternlogq	VR\c1, VR\l6, VR\l11, 0x96
	vpternlogq	VR\c2, VR\l7, VR\l12, 0x96
	vpternlogq	VR\c3, VR\l8, VR\l13, 0x96
	vpternlogq	VR\c4, VR\l9, VR\l14, 0x96
	vpternlogq	VR\c0, VR\l15, VR\l20, 0x96
	VHOOK		t
	vpternlogq	VR\c1, VR\l16, VR\l21, 0x96
	VHOOK		t
	vpternlogq	VR\c2, VR\l17, VR\l22, 0x96
	VHOOK		t
	vpternlogq	VR\c3, VR\l18, VR\l23, 0x96
	VHOOK		t
	vpternlogq	VR\c4, VR\l19, VR\l24, 0x96
	VHOOK		t
	vprolq		VR\t0, VR\c1, 1			/* D0 = C4 ^ rotl(C1) */
	vpxorq		VR\t0, VR\t0, VR\c4
	vprolq		VR\t1, VR\c2, 1			/* D1 = C0 ^ rotl(C2) */
	vpxorq		VR\t1, VR\t1, VR\c0
	VHOOK		t
	vprolq		VR\c0, VR\c0, 1			/* D4 = C3 ^ rotl(C0) */
	vpxorq		VR\c0, VR\c0, VR\c3
	vprolq		VR\c3, VR\c3, 1			/* D2 = C1 ^ rotl(C3) */
	vpxorq		VR\c3, VR\c3, VR\c1
	VHOOK		t
	vprolq		VR\c4, VR\c4, 1			/* D3 = C2 ^ rotl(C4) */
	vpxorq		VR\c4, VR\c4, VR\c2
	VHOOK		t
.endm

/* B = rotl(A ^ D, rot), in place */
.macro LANE_D a, d, rot
	vpxorq		VR\a, VR\a, VR\d
.if \rot == 8
	vpshufb		VR\a, VR\a, ROT8
.elseif \rot == 56
	vpshufb		VR\a, VR\a, ROT56
.elseif \rot
	vprolq		VR\a, VR\a, \rot
.endif
	VHOOK		r
.endm

/* chi over one row b0..b4: outputs x = 0, 1 to the free registers t0, t1,
 * x = 2, 3, 4 in place (b_x can take its own output once the later outputs
 * no longer need it); b0, b1 are free afterwards */
.macro CHI_ROW_D b0, b1, b2, b3, b4, t0, t1
	vmovdqa64	VR\t0, VR\b0
	vpternlogq	VR\t0, VR\b1, VR\b2, 0xD2
	VHOOK		c
	vmovdqa64	VR\t1, VR\b1
	vpternlogq	VR\t1, VR\b2, VR\b3, 0xD2
	VHOOK		c
	vpternlogq	VR\b2, VR\b3, VR\b4, 0xD2
	VHOOK		c
	vpternlogq	VR\b3, VR\b4, VR\b0, 0xD2
	VHOOK		c
	vpternlogq	VR\b4, VR\b0, VR\b1, 0xD2
	VHOOK		c
.endm

/* chi over row 0 of round r, with iota */
.macro CHI_ROW0_D r, b0, b1, b2, b3, b4, t0, t1
	vmovdqa64	VR\t0, VR\b0
	vpternlogq	VR\t0, VR\b1, VR\b2, 0xD2
.if LOOP_RC
	vpxorq		VR\t0, VR\t0, RCL(\r - 1)
.else
	vpxorq		VR\t0, VR\t0, RC(\r)
.endif
	VHOOK		c
	vmovdqa64	VR\t1, VR\b1
	vpternlogq	VR\t1, VR\b2, VR\b3, 0xD2
	VHOOK		c
	vpternlogq	VR\b2, VR\b3, VR\b4, 0xD2
	VHOOK		c
	vpternlogq	VR\b3, VR\b4, VR\b0, 0xD2
	VHOOK		c
	vpternlogq	VR\b4, VR\b0, VR\b1, 0xD2
	VHOOK		c
.endm

/*
 * One full round r (1..22) on lanes l0..l24 with the free registers
 * f0..f6. Row y gathers B[x] from lane ((x+3y)%5) + 5x (pi); D[x] applies
 * to the lanes with that x, i.e. D0 = f5, D1 = f6, D2 = f3, D3 = f4,
 * D4 = f0 after THETA_D. The next round finds
 *   lanes 0..4   in f1,  f2,  l12, l18, l24
 *   lanes 5..9   in l0,  l6,  l10, l16, l22
 *   lanes 10..14 in l3,  l9,  l13, l19, l20
 *   lanes 15..19 in l1,  l7,  l11, l17, l23
 *   lanes 20..24 in l4,  l5,  l14, l15, l21    free: l2, l8, f5, f6, f3, f4, f0
 */
.macro ROUND_D r, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, \
		l15, l16, l17, l18, l19, l20, l21, l22, l23, l24, f0, f1, f2, f3, f4, f5, f6
	RHOOK_BEGIN	\r
	THETA_D	\l0, \l1, \l2, \l3, \l4, \l5, \l6, \l7, \l8, \l9, \l10, \l11, \l12, \l13, \l14, \
		\l15, \l16, \l17, \l18, \l19, \l20, \l21, \l22, \l23, \l24, \f0, \f1, \f2, \f3, \f4, \f5, \f6
	/* row 0: lanes 0, 6, 12, 18, 24 */
	LANE_D		\l0,  \f5, 0
	LANE_D		\l6,  \f6, R6
	LANE_D		\l12, \f3, R12
	LANE_D		\l18, \f4, R18
	LANE_D		\l24, \f0, R24
	CHI_ROW0_D	\r, \l0, \l6, \l12, \l18, \l24, \f1, \f2
	/* row 1: lanes 3, 9, 10, 16, 22 */
	LANE_D		\l3,  \f4, R3
	LANE_D		\l9,  \f0, R9
	LANE_D		\l10, \f5, R10
	LANE_D		\l16, \f6, R16
	LANE_D		\l22, \f3, R22
	CHI_ROW_D	\l3, \l9, \l10, \l16, \l22, \l0, \l6
	/* row 2: lanes 1, 7, 13, 19, 20 */
	LANE_D		\l1,  \f6, R1
	LANE_D		\l7,  \f3, R7
	LANE_D		\l13, \f4, R13
	LANE_D		\l19, \f0, R19
	LANE_D		\l20, \f5, R20
	CHI_ROW_D	\l1, \l7, \l13, \l19, \l20, \l3, \l9
	/* row 3: lanes 4, 5, 11, 17, 23 */
	LANE_D		\l4,  \f0, R4
	LANE_D		\l5,  \f5, R5
	LANE_D		\l11, \f6, R11
	LANE_D		\l17, \f3, R17
	LANE_D		\l23, \f4, R23
	CHI_ROW_D	\l4, \l5, \l11, \l17, \l23, \l1, \l7
	/* row 4: lanes 2, 8, 14, 15, 21 */
	LANE_D		\l2,  \f3, R2
	LANE_D		\l8,  \f4, R8
	LANE_D		\l14, \f0, R14
	LANE_D		\l15, \f5, R15
	LANE_D		\l21, \f6, R21
	CHI_ROW_D	\l2, \l8, \l14, \l15, \l21, \l4, \l5
	RHOOK_END
.endm

/* Round 23: theta, then row 0 only, x = 0..3. The digest words end up in
 * f2, l6, l12, l18 and go to OUTPUT with eight of the dead registers as
 * its scratch. */
.macro LAST_ROUND_D l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, \
		l15, l16, l17, l18, l19, l20, l21, l22, l23, l24, f0, f1, f2, f3, f4, f5, f6
	RHOOK_BEGIN	23
	THETA_D	\l0, \l1, \l2, \l3, \l4, \l5, \l6, \l7, \l8, \l9, \l10, \l11, \l12, \l13, \l14, \
		\l15, \l16, \l17, \l18, \l19, \l20, \l21, \l22, \l23, \l24, \f0, \f1, \f2, \f3, \f4, \f5, \f6
	LANE_D		\l0,  \f5, 0
	LANE_D		\l6,  \f6, R6
	LANE_D		\l12, \f3, R12
	LANE_D		\l18, \f4, R18
	LANE_D		\l24, \f0, R24
	vmovdqa64	VR\f2, VR\l0
	vpternlogq	VR\f2, VR\l6, VR\l12, 0xD2
	vpxorq		VR\f2, VR\f2, RC(23)
	vpternlogq	VR\l6, VR\l12, VR\l18, 0xD2
	vpternlogq	VR\l12, VR\l18, VR\l24, 0xD2
	vpternlogq	VR\l18, VR\l24, VR\l0, 0xD2
	OUTPUT		\f2, \l6, \l12, \l18, \f0, \f1, \f3, \f4, \f5, \f6, \l1, \l2
	RHOOK_END
.endm

/*
 * Round 0. Expects word j of every node in register j (j = 0..7);
 * registers 8..31 are free. Only lanes 0..7, 8 (= 0x01) and 16
 * (= 0x80..00) are non-zero, so theta computes C[0..3] in 22..25 (C4 is
 * lane 4 itself) and D[0..4] in 27..31 directly, a zero lane's B is just
 * rotl(D, r) into a free register, and the chi temporaries come from the
 * free registers too. Leaves the lanes in
 *   11, 12, 8, 9, 10, 17, 18, 14, 15, 16, 22, 23, 19, 20, 21, 0, 6, 24,
 *   25, 26, 4, 5, 13, 1, 7     free: 2, 3, 27, 28, 29, 30, 31
 */
.macro KECCAK_ROUND0_D
	RHOOK_BEGIN	0
	vpxorq		VREG(22), VREG(0), VREG(5)
	vpxorq		VREG(23), VREG(1), VREG(6)
	vpxorq		VREG(23), VREG(23), K63
	vpxorq		VREG(24), VREG(2), VREG(7)
	vpxorq		VREG(25), VREG(3), K1
	vprolq		VREG(27), VREG(23), 1
	VHOOK		t
	vpxorq		VREG(27), VREG(27), VREG(4)	/* D0 = C4 ^ rotl(C1) */
	vprolq		VREG(28), VREG(24), 1
	VHOOK		t
	vpxorq		VREG(28), VREG(28), VREG(22)	/* D1 = C0 ^ rotl(C2) */
	vprolq		VREG(29), VREG(25), 1
	VHOOK		t
	vpxorq		VREG(29), VREG(29), VREG(23)	/* D2 = C1 ^ rotl(C3) */
	vprolq		VREG(30), VREG(4), 1
	vpxorq		VREG(30), VREG(30), VREG(24)	/* D3 = C2 ^ rotl(C4) */
	vprolq		VREG(31), VREG(22), 1
	VHOOK		t
	vpxorq		VREG(31), VREG(31), VREG(25)	/* D4 = C3 ^ rotl(C0) */
	/* row 0: lanes 0, 6, 12, 18, 24 -> 11, 12, 8, 9, 10 */
	vpxorq		VREG(0), VREG(0), VREG(27)
	VHOOK		r
	vpxorq		VREG(6), VREG(6), VREG(28)
	vprolq		VREG(6), VREG(6), R6
	VHOOK		r
	vprolq		VREG(8), VREG(29), R12
	VHOOK		r
	vprolq		VREG(9), VREG(30), R18
	VHOOK		r
	vprolq		VREG(10), VREG(31), R24
	VHOOK		r
	CHI_ROW0_D	0, 0, 6, 8, 9, 10, 11, 12
	/* row 1: lanes 3, 9, 10, 16, 22 -> 17, 18, 14, 15, 16 */
	vpxorq		VREG(3), VREG(3), VREG(30)
	vprolq		VREG(3), VREG(3), R3
	VHOOK		r
	vprolq		VREG(13), VREG(31), R9
	VHOOK		r
	vprolq		VREG(14), VREG(27), R10
	VHOOK		r
	vpxorq		VREG(15), VREG(28), K63		/* padding lane 16 */
	vprolq		VREG(15), VREG(15), R16
	VHOOK		r
	vprolq		VREG(16), VREG(29), R22
	VHOOK		r
	CHI_ROW_D	3, 13, 14, 15, 16, 17, 18
	/* row 2: lanes 1, 7, 13, 19, 20 -> 22, 23, 19, 20, 21 */
	vpxorq		VREG(1), VREG(1), VREG(28)
	vprolq		VREG(1), VREG(1), R1
	VHOOK		r
	vpxorq		VREG(7), VREG(7), VREG(29)
	vprolq		VREG(7), VREG(7), R7
	VHOOK		r
	vprolq		VREG(19), VREG(30), R13
	VHOOK		r
	vpshufb		VREG(20), VREG(31), ROT8	/* R19 = 8 */
	VHOOK		r
	vprolq		VREG(21), VREG(27), R20
	VHOOK		r
	CHI_ROW_D	1, 7, 19, 20, 21, 22, 23
	/* row 3: lanes 4, 5, 11, 17, 23 -> 0, 6, 24, 25, 26 */
	vpxorq		VREG(4), VREG(4), VREG(31)
	vprolq		VREG(4), VREG(4), R4
	VHOOK		r
	vpxorq		VREG(5), VREG(5), VREG(27)
	vprolq		VREG(5), VREG(5), R5
	VHOOK		r
	vprolq		VREG(24), VREG(28), R11
	VHOOK		r
	vprolq		VREG(25), VREG(29), R17
	VHOOK		r
	vpshufb		VREG(26), VREG(30), ROT56	/* R23 = 56 */
	VHOOK		r
	CHI_ROW_D	4, 5, 24, 25, 26, 0, 6
	/* row 4: lanes 2, 8, 14, 15, 21 -> 4, 5, 13, 1, 7 */
	vpxorq		VREG(2), VREG(2), VREG(29)
	vprolq		VREG(2), VREG(2), R2
	VHOOK		r
	vpxorq		VREG(3), VREG(30), K1		/* padding lane 8 */
	vprolq		VREG(3), VREG(3), R8
	VHOOK		r
	vprolq		VREG(13), VREG(31), R14
	VHOOK		r
	vprolq		VREG(1), VREG(27), R15
	VHOOK		r
	vprolq		VREG(7), VREG(28), R21
	VHOOK		r
	CHI_ROW_D	2, 3, 13, 1, 7, 4, 5
	RHOOK_END
.endm

/* The whole permutation, unrolled: each ROUND_D line is the placement the
 * previous round left behind (see ROUND_D); the constants are
 * rip-relative. */
.macro KECCAK_F_D
	KECCAK_ROUND0_D
	ROUND_D	1, 11, 12, 8, 9, 10, 17, 18, 14, 15, 16, 22, 23, 19, 20, 21, 0, 6, 24, 25, 26, 4, 5, 13, 1, 7, 2, 3, 27, 28, 29, 30, 31
	ROUND_D	2, 3, 27, 19, 25, 7, 11, 18, 22, 6, 13, 9, 16, 20, 26, 4, 12, 14, 23, 24, 1, 10, 17, 21, 0, 5, 8, 15, 30, 31, 28, 29, 2
	ROUND_D	3, 15, 30, 20, 24, 5, 3, 18, 9, 14, 21, 25, 13, 26, 1, 10, 27, 22, 16, 23, 0, 7, 11, 4, 12, 17, 19, 6, 29, 2, 31, 28, 8
	ROUND_D	4, 6, 29, 26, 23, 17, 15, 18, 25, 22, 4, 24, 21, 1, 0, 7, 30, 9, 13, 16, 12, 5, 3, 10, 27, 11, 20, 14, 28, 8, 2, 31, 19
	ROUND_D	5, 14, 28, 1, 16, 11, 6, 18, 24, 9, 10, 23, 4, 0, 12, 5, 29, 25, 21, 13, 27, 17, 15, 7, 30, 3, 26, 22, 31, 19, 8, 2, 20
	ROUND_D	6, 22, 31, 0, 13, 3, 14, 18, 23, 25, 7, 16, 10, 12, 27, 17, 28, 24, 4, 21, 30, 11, 6, 5, 29, 15, 1, 9, 2, 20, 19, 8, 26
	ROUND_D	7, 9, 2, 12, 21, 15, 22, 18, 16, 24, 5, 13, 7, 27, 30, 11, 31, 23, 10, 4, 29, 3, 14, 17, 28, 6, 0, 25, 8, 26, 20, 19, 1
	ROUND_D	8, 25, 8, 27, 4, 6, 9, 18, 13, 23, 17, 21, 5, 30, 29, 3, 2, 16, 7, 10, 28, 15, 22, 11, 31, 14, 12, 24, 19, 1, 26, 20, 0
	ROUND_D	9, 24, 19, 30, 10, 14, 25, 18, 21, 16, 11, 4, 17, 29, 28, 15, 8, 13, 5, 7, 31, 6, 9, 3, 2, 22, 27, 23, 20, 0, 1, 26, 12
	ROUND_D	10, 23, 20, 29, 7, 22, 24, 18, 4, 13, 3, 10, 11, 28, 31, 6, 19, 21, 17, 5, 2, 14, 25, 15, 8, 9, 30, 16, 26, 12, 0, 1, 27
	ROUND_D	11, 16, 26, 28, 5, 9, 23, 18, 10, 21, 15, 7, 3, 31, 2, 14, 20, 4, 11, 17, 8, 22, 24, 6, 19, 25, 29, 13, 1, 27, 12, 0, 30
	ROUND_D	12, 13, 1, 31, 17, 25, 16, 18, 7, 4, 6, 5, 15, 2, 8, 22, 26, 10, 3, 11, 19, 9, 23, 14, 20, 24, 28, 21, 0, 30, 27, 12, 29
	ROUND_D	13, 21, 0, 2, 11, 24, 13, 18, 5, 10, 14, 17, 6, 8, 19, 9, 1, 7, 15, 3, 20, 25, 16, 22, 26, 23, 31, 4, 12, 29, 30, 27, 28
	ROUND_D	14, 4, 12, 8, 3, 23, 21, 18, 17, 7, 22, 11, 14, 19, 20, 25, 0, 5, 6, 15, 26, 24, 13, 9, 1, 16, 2, 10, 27, 28, 29, 30, 31
	ROUND_D	15, 10, 27, 19, 15, 16, 4, 18, 11, 5, 9, 3, 22, 20, 26, 24, 12, 17, 14, 6, 1, 23, 21, 25, 0, 13, 8, 7, 30, 31, 28, 29, 2
	ROUND_D	16, 7, 30, 20, 6, 13, 10, 18, 3, 17, 25, 15, 9, 26, 1, 23, 27, 11, 22, 14, 0, 16, 4, 24, 12, 21, 19, 5, 29, 2, 31, 28, 8
	ROUND_D	17, 5, 29, 26, 14, 21, 7, 18, 15, 11, 24, 6, 25, 1, 0, 16, 30, 3, 9, 22, 12, 13, 10, 23, 27, 4, 20, 17, 28, 8, 2, 31, 19
	ROUND_D	18, 17, 28, 1, 22, 4, 5, 18, 6, 3, 23, 14, 24, 0, 12, 13, 29, 15, 25, 9, 27, 21, 7, 16, 30, 10, 26, 11, 31, 19, 8, 2, 20
	ROUND_D	19, 11, 31, 0, 9, 10, 17, 18, 14, 15, 16, 22, 23, 12, 27, 21, 28, 6, 24, 25, 30, 4, 5, 13, 29, 7, 1, 3, 2, 20, 19, 8, 26
	ROUND_D	20, 3, 2, 12, 25, 7, 11, 18, 22, 6, 13, 9, 16, 27, 30, 4, 31, 14, 23, 24, 29, 10, 17, 21, 28, 5, 0, 15, 8, 26, 20, 19, 1
	ROUND_D	21, 15, 8, 27, 24, 5, 3, 18, 9, 14, 21, 25, 13, 30, 29, 10, 2, 22, 16, 23, 28, 7, 11, 4, 31, 17, 12, 6, 19, 1, 26, 20, 0
	ROUND_D	22, 6, 19, 30, 23, 17, 15, 18, 25, 22, 4, 24, 21, 29, 28, 7, 8, 9, 13, 16, 31, 5, 3, 10, 2, 11, 27, 14, 20, 0, 1, 26, 12
	LAST_ROUND_D	14, 20, 29, 16, 11, 6, 18, 24, 9, 10, 23, 4, 28, 31, 5, 19, 25, 21, 13, 2, 17, 15, 7, 8, 3, 30, 22, 26, 12, 0, 1, 27
.endm

/* The same permutation with rounds 1..20 as five iterations of a
 * four-round loop (see keccak256_avx512.inc for why: the unrolled version
 * does not fit the decoded-instruction caches). After four rounds the lane
 * placement differs from the loop's entry placement by a fixed
 * permutation; these 25 copies restore it. The round constant comes from
 * [RCP + 8*k] for round k of the body (RCL in the including file); RCP is
 * clobbered and the iteration count lives in the stack slot LOOP_CNT. */
.macro LOOP_RESTORE_D
	vmovdqa64	VREG(8), VREG(1)
	vmovdqa64	VREG(22), VREG(23)
	vmovdqa64	VREG(23), VREG(4)
	vmovdqa64	VREG(19), VREG(0)
	vmovdqa64	VREG(20), VREG(12)
	vmovdqa64	VREG(12), VREG(28)
	vmovdqa64	VREG(0), VREG(29)
	vmovdqa64	VREG(26), VREG(27)
	vmovdqa64	VREG(4), VREG(17)
	vmovdqa64	VREG(17), VREG(6)
	vmovdqa64	VREG(6), VREG(25)
	vmovdqa64	VREG(25), VREG(13)
	vmovdqa64	VREG(13), VREG(7)
	vmovdqa64	VREG(1), VREG(30)
	vmovdqa64	VREG(7), VREG(3)
	vmovdqa64	VREG(31), VREG(11)
	vmovdqa64	VREG(11), VREG(14)
	vmovdqa64	VREG(14), VREG(24)
	vmovdqa64	VREG(24), VREG(21)
	vmovdqa64	VREG(21), VREG(5)
	vmovdqa64	VREG(5), VREG(15)
	vmovdqa64	VREG(15), VREG(9)
	vmovdqa64	VREG(9), VREG(16)
	vmovdqa64	VREG(16), VREG(10)
	vmovdqa64	VREG(10), VREG(31)
.endm

.macro KECCAK_F_D_LOOP
	lea		RCP, [rip + .LKECCAK_RC]
	KECCAK_ROUND0_D
	add		RCP, 8
	mov		qword ptr [LOOP_CNT], 5
	.set		LOOP_RC, 1
1:
	ROUND_D	1, 11, 12, 8, 9, 10, 17, 18, 14, 15, 16, 22, 23, 19, 20, 21, 0, 6, 24, 25, 26, 4, 5, 13, 1, 7, 2, 3, 27, 28, 29, 30, 31
	ROUND_D	2, 3, 27, 19, 25, 7, 11, 18, 22, 6, 13, 9, 16, 20, 26, 4, 12, 14, 23, 24, 1, 10, 17, 21, 0, 5, 8, 15, 30, 31, 28, 29, 2
	ROUND_D	3, 15, 30, 20, 24, 5, 3, 18, 9, 14, 21, 25, 13, 26, 1, 10, 27, 22, 16, 23, 0, 7, 11, 4, 12, 17, 19, 6, 29, 2, 31, 28, 8
	ROUND_D	4, 6, 29, 26, 23, 17, 15, 18, 25, 22, 4, 24, 21, 1, 0, 7, 30, 9, 13, 16, 12, 5, 3, 10, 27, 11, 20, 14, 28, 8, 2, 31, 19
	LOOP_RESTORE_D
	add		RCP, 32
	dec		qword ptr [LOOP_CNT]
	jnz		1b
	.set		LOOP_RC, 0
	ROUND_D	21, 11, 12, 8, 9, 10, 17, 18, 14, 15, 16, 22, 23, 19, 20, 21, 0, 6, 24, 25, 26, 4, 5, 13, 1, 7, 2, 3, 27, 28, 29, 30, 31
	ROUND_D	22, 3, 27, 19, 25, 7, 11, 18, 22, 6, 13, 9, 16, 20, 26, 4, 12, 14, 23, 24, 1, 10, 17, 21, 0, 5, 8, 15, 30, 31, 28, 29, 2
	LAST_ROUND_D	15, 30, 20, 24, 5, 3, 18, 9, 14, 21, 25, 13, 26, 1, 10, 27, 22, 16, 23, 0, 7, 11, 4, 12, 17, 19, 6, 29, 2, 31, 28, 8
.endm
