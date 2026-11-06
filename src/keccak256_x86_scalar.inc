/*
 * Keccak-f[1600] on one node in the x86-64 general registers, shared by
 * keccak256_x86_x1.S (and open to interleaving with a vector kernel).
 *
 * 15 registers cannot hold the 25-lane state, so the state lives in two
 * 25-lane buffers on the stack and each round reads one and writes the
 * other, row by row (keccak256_avx2.inc does the same with vectors).
 * The registers hold one row of B, the theta terms D0..D3, and the column
 * parities C0..C4, which chi accumulates as it stores the new state, so
 * theta never re-reads it. That is 15 registers plus the one temporary
 * chi needs, so D4 is spilled: the five lanes of column 4 take it as a
 * memory operand (a load, no extra ALU work) and the out-of-order core
 * runs them last.
 *
 * Per round (ALU operations; loads and stores go to the address units):
 *   theta:  D[x] = C[x-1] ^ rotl(C[x+1], 1)      5 rorx + 5 xor
 *   rho/pi: B = rotl(A ^ D[x], r)                25 xor (memory operand)
 *                                                + 24 rorx
 *   chi:    A' = B[x] ^ (~B[x+1] & B[x+2])       25 andn + 25 xor
 *   iota:   A'[0] ^= RC                          1 xor (memory operand)
 *   parity: C' = A'[x,0]^..^A'[x,4]              20 xor (row 0 is a copy)
 * = 130 ALU operations, 32.5 cycles on the four ALUs of a Zen 3 / Golden
 * Cove class core; the lane loads come first in each rho so they issue
 * while D is still in flight. rorx (BMI2) and andn (BMI1) are three-
 * operand and flag-free: no mov, no not, no flag merges.
 *
 * Round 0 skips the 15 zero lanes (B = rotl(D), one rorx) and folds in the
 * two padding constants; round 23 computes only the 4 output lanes.
 *
 * The including file names the registers B0..B4, C0..C4, D0..D3, T and
 * sets the rsp offsets of the two state buffers (S0, S1), the D4 spill
 * slot (D4S) and the output pointer slot (OUTP); the round constants are
 * .LKECCAK_RC (KECCAK_RODATA in keccak256_x86_frame.inc).
 */
#define LANE(buf, i)	qword ptr [rsp + (buf) + 8*(i)]
#define D4M		qword ptr [rsp + D4S]

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

/* d = c1 ^ rotl(c2, 1) */
.macro THETA_D d, c1, c2
	rorx		\d, \c2, 63
	xor		\d, \c1
.endm

/* D0..D3 and the D4 slot from the parities C0..C4 (C is free after) */
.macro THETA
	THETA_D		D0, C4, C1
	THETA_D		D1, C0, C2
	THETA_D		D2, C1, C3
	THETA_D		D3, C2, C4
	THETA_D		T, C3, C0
	mov		D4M, T
.endm

/* b = rotl(A[i] ^ d, rot) with A[i] from the state at buf; d is a
 * register or the literal D4 (the spill slot) */
.macro THETA_RHO b, d, buf, i, rot
	mov		\b, LANE(\buf, \i)
.ifc \d, D4
	xor		\b, D4M
.else
	xor		\b, \d
.endif
.if \rot
	rorx		\b, \b, 64 - \rot
.endif
.endm

/* out[x] = B[x] ^ (~B[x+1] & B[x+2]), stored to lane i of the state at buf
 * and folded into the next round's parity c (row 0 starts it: its outputs
 * go straight into the C registers, which theta has consumed). Lane 0 takes
 * the iota constant RC[rc]. */
.macro CHI c, b0, b1, b2, buf, i, rc
.if \i < 5
	andn		\c, \b1, \b2
	xor		\c, \b0
.if \i == 0
	xor		\c, qword ptr [rip + .LKECCAK_RC + 8*\rc]
.endif
	mov		LANE(\buf, \i), \c
.else
	andn		T, \b1, \b2
	xor		T, \b0
	mov		LANE(\buf, \i), T
	xor		\c, T
.endif
.endm

/* chi over B0..B4 into row y of the state at buf */
.macro CHI_ROW buf, y, rc
	CHI		C0, B0, B1, B2, \buf, 5*\y + 0, \rc
	CHI		C1, B1, B2, B3, \buf, 5*\y + 1, \rc
	CHI		C2, B2, B3, B4, \buf, 5*\y + 2, \rc
	CHI		C3, B3, B4, B0, \buf, 5*\y + 3, \rc
	CHI		C4, B4, B0, B1, \buf, 5*\y + 4, \rc
.endm

/* one round from the state at in to out with the constant RC[rc];
 * parities in C0..C4 on entry and exit. Row y gathers B[x] from lane
 * ((x+3y)%5) + 5x (pi), so its D index is (x+3y)%5. */
.macro ROUND in, out, rc
	THETA
	THETA_RHO	B0, D0, \in, 0,  0
	THETA_RHO	B1, D1, \in, 6,  R6
	THETA_RHO	B2, D2, \in, 12, R12
	THETA_RHO	B3, D3, \in, 18, R18
	THETA_RHO	B4, D4, \in, 24, R24
	CHI_ROW		\out, 0, \rc
	THETA_RHO	B0, D3, \in, 3,  R3
	THETA_RHO	B1, D4, \in, 9,  R9
	THETA_RHO	B2, D0, \in, 10, R10
	THETA_RHO	B3, D1, \in, 16, R16
	THETA_RHO	B4, D2, \in, 22, R22
	CHI_ROW		\out, 1, \rc
	THETA_RHO	B0, D1, \in, 1,  R1
	THETA_RHO	B1, D2, \in, 7,  R7
	THETA_RHO	B2, D3, \in, 13, R13
	THETA_RHO	B3, D4, \in, 19, R19
	THETA_RHO	B4, D0, \in, 20, R20
	CHI_ROW		\out, 2, \rc
	THETA_RHO	B0, D4, \in, 4,  R4
	THETA_RHO	B1, D0, \in, 5,  R5
	THETA_RHO	B2, D1, \in, 11, R11
	THETA_RHO	B3, D2, \in, 17, R17
	THETA_RHO	B4, D3, \in, 23, R23
	CHI_ROW		\out, 3, \rc
	THETA_RHO	B0, D2, \in, 2,  R2
	THETA_RHO	B1, D3, \in, 8,  R8
	THETA_RHO	B2, D4, \in, 14, R14
	THETA_RHO	B3, D0, \in, 15, R15
	THETA_RHO	B4, D1, \in, 21, R21
	CHI_ROW		\out, 4, \rc
.endm

/* round 0 lanes: zero lane (B = rotl(D)) and the two padding lanes
 * (B = rotl(K ^ D)); every zero lane has a nonzero rho offset */
.macro RHO_ZERO b, d, rot
.ifc \d, D4
	rorx		\b, D4M, 64 - \rot
.else
	rorx		\b, \d, 64 - \rot
.endif
.endm
.macro RHO_PAD1 b, d, rot
	mov		\b, \d
	xor		\b, 1
	rorx		\b, \b, 64 - \rot
.endm
.macro RHO_PAD63 b, d, rot
	mov		\b, \d
	btc		\b, 63
	rorx		\b, \b, 64 - \rot
.endm

/* round 0: the node's 8 words in B0..B4, C0..C2 (lanes 0..7; also stored
 * to lanes 0..7 of the state at in for the row loads), lane 8 = 0x01,
 * lane 16 = 0x80..00, the rest zero. Writes the state at out with the
 * parities in C0..C4. */
.macro ROUND0 in, out
	mov		LANE(\in, 0), B0
	mov		LANE(\in, 1), B1
	mov		LANE(\in, 2), B2
	mov		LANE(\in, 3), B3
	mov		LANE(\in, 4), B4
	mov		LANE(\in, 5), C0
	mov		LANE(\in, 6), C1
	mov		LANE(\in, 7), C2
	xor		C0, B0
	xor		C1, B1
	btc		C1, 63
	xor		C2, B2
	mov		C3, B3
	xor		C3, 1
	mov		C4, B4
	THETA
	THETA_RHO	B0, D0, \in, 0,  0
	THETA_RHO	B1, D1, \in, 6,  R6
	RHO_ZERO	B2, D2, R12
	RHO_ZERO	B3, D3, R18
	RHO_ZERO	B4, D4, R24
	CHI_ROW		\out, 0, 0
	THETA_RHO	B0, D3, \in, 3,  R3
	RHO_ZERO	B1, D4, R9
	RHO_ZERO	B2, D0, R10
	RHO_PAD63	B3, D1, R16
	RHO_ZERO	B4, D2, R22
	CHI_ROW		\out, 1, 0
	THETA_RHO	B0, D1, \in, 1,  R1
	THETA_RHO	B1, D2, \in, 7,  R7
	RHO_ZERO	B2, D3, R13
	RHO_ZERO	B3, D4, R19
	RHO_ZERO	B4, D0, R20
	CHI_ROW		\out, 2, 0
	THETA_RHO	B0, D4, \in, 4,  R4
	THETA_RHO	B1, D0, \in, 5,  R5
	RHO_ZERO	B2, D1, R11
	RHO_ZERO	B3, D2, R17
	RHO_ZERO	B4, D3, R23
	CHI_ROW		\out, 3, 0
	THETA_RHO	B0, D2, \in, 2,  R2
	RHO_PAD1	B1, D3, R8
	RHO_ZERO	B2, D4, R14
	RHO_ZERO	B3, D0, R15
	RHO_ZERO	B4, D1, R21
	CHI_ROW		\out, 4, 0
.endm

/* round 23 from the state at in: theta, then row 0, x = 0..3 only, stored
 * as the digest at the output pointer in [rsp + OUTP] */
.macro ROUND23 in
	THETA
	THETA_RHO	B0, D0, \in, 0,  0
	THETA_RHO	B1, D1, \in, 6,  R6
	THETA_RHO	B2, D2, \in, 12, R12
	THETA_RHO	B3, D3, \in, 18, R18
	THETA_RHO	B4, D4, \in, 24, R24
	mov		C0, qword ptr [rsp + OUTP]
	andn		C1, B1, B2
	xor		C1, B0
	xor		C1, qword ptr [rip + .LKECCAK_RC + 8*23]
	andn		C2, B2, B3
	xor		C2, B1
	andn		C3, B3, B4
	xor		C3, B2
	andn		C4, B4, B0
	xor		C4, B3
	mov		qword ptr [C0 + 0], C1
	mov		qword ptr [C0 + 8], C2
	mov		qword ptr [C0 + 16], C3
	mov		qword ptr [C0 + 24], C4
.endm

/* rounds 0..23 of one node: the 8 input words in B0..B4, C0..C2, the
 * digest to [[rsp + OUTP]] */
.macro KECCAK_X1
	ROUND0		S0, S1
	ROUND		S1, S0, 1
	ROUND		S0, S1, 2
	ROUND		S1, S0, 3
	ROUND		S0, S1, 4
	ROUND		S1, S0, 5
	ROUND		S0, S1, 6
	ROUND		S1, S0, 7
	ROUND		S0, S1, 8
	ROUND		S1, S0, 9
	ROUND		S0, S1, 10
	ROUND		S1, S0, 11
	ROUND		S0, S1, 12
	ROUND		S1, S0, 13
	ROUND		S0, S1, 14
	ROUND		S1, S0, 15
	ROUND		S0, S1, 16
	ROUND		S1, S0, 17
	ROUND		S0, S1, 18
	ROUND		S1, S0, 19
	ROUND		S0, S1, 20
	ROUND		S1, S0, 21
	ROUND		S0, S1, 22
	ROUND23		S1
.endm
