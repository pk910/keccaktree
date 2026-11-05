/*
 * void keccaktree_keccak256_avx2_x4(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 4 at a time: node j
 * of a batch lives in qword lane j of every ymm register. AVX2.
 *
 * AVX2 has 16 ymm registers, too few for the 25-lane state, so the state
 * lives in two 25-lane buffers on the stack and each round reads one and
 * writes the other; rounds 1..22 are therefore a plain loop. Registers hold
 * D[0..4], one row of B, and the column parities C[0..4], which chi
 * accumulates as it stores the new state, so theta never re-reads it:
 *
 *   theta:  D[x] = C[x-1] ^ rotl(C[x+1], 1)      20 ops
 *   rho/pi: B = rotl(A ^ D[x], r)                25 vpxor (memory operand)
 *                                                + 24 rotations (3 ops; 8 and
 *                                                56 are one vpshufb)
 *   chi:    A' = B[x] ^ (~B[x+1] & B[x+2])       25 vpandn + 25 vpxor
 *   iota:   A'[0] ^= RC                          1 vpxor
 *   parity: C' = A'[x,0]^..^A'[x,4]              20 vpxor
 *
 * Round 0 skips the 15 zero lanes and folds in the two padding constants;
 * round 23 computes only the 4 output lanes. A single node goes to the
 * scalar code, which is faster than a padded batch.
 *
 * Registers: ymm0..15; rcx, rsi, r8 here and the frame's r9..r11.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#define NODES		4
#define VBYTES		32
#define SLOTS		(50*32)			/* the two state buffers */
#define SMALL_TAIL	keccaktree_keccak256_generic	/* a single node: scalar is faster */
#define SMALL_TAIL_MAX	1
#include "keccak256_x86_frame.inc"

#define BUF0		r9			/* = rsp, state buffer 0 */
#define BUF1		r8			/* state buffer 1 */
#define RCP		rsi			/* round constants (broadcast) */
#define LANE(base, i)	ymmword ptr [base + 32*(i)]

#define D0 ymm0
#define D1 ymm1
#define D2 ymm2
#define D3 ymm3
#define D4 ymm4
#define B0 ymm5
#define B1 ymm6
#define B2 ymm7
#define B3 ymm8
#define B4 ymm9
#define C0 ymm10
#define C1 ymm11
#define C2 ymm12
#define C3 ymm13
#define C4 ymm14
#define T  ymm15

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

/* b = rotl(b, n) in place; t is a scratch register */
.macro ROL b, n, t
.if \n == 8
	vpshufb		\b, \b, ymmword ptr [rip + .LROT8]
.elseif \n == 56
	vpshufb		\b, \b, ymmword ptr [rip + .LROT56]
.elseif \n == 1
	vpsrlq		\t, \b, 63
	vpaddq		\b, \b, \b
	vpor		\b, \b, \t
.elseif \n
	vpsrlq		\t, \b, 64 - \n
	vpsllq		\b, \b, \n
	vpor		\b, \b, \t
.endif
.endm

/* d = c1 ^ rotl(c2, 1); t is a scratch register */
.macro THETA_D d, c1, c2, t
	vpaddq		\d, \c2, \c2
	vpsrlq		\t, \c2, 63
	vpor		\d, \d, \t
	vpxor		\d, \d, \c1
.endm

/* theta: D0..D4 from the column parities C0..C4 */
.macro THETA
	THETA_D		D0, C4, C1, T
	THETA_D		D1, C0, C2, T
	THETA_D		D2, C1, C3, T
	THETA_D		D3, C2, C4, T
	THETA_D		D4, C3, C0, T
.endm

/* b = rotl(A[i] ^ d, rot) with A[i] from memory */
.macro THETA_RHO b, d, base, i, rot
	vpxor		\b, \d, LANE(\base, \i)
	ROL		\b, \rot, T
.endm

/* out[x] = B[x] ^ (~B[x+1] & B[x+2]), stored to lane i of the state at
 * base and folded into the next round's parity c (row 0 starts it) */
.macro CHI c, b0, b1, b2, base, i, rc
.if \i < 5
	vpandn		\c, \b1, \b2
	vpxor		\c, \c, \b0
.if \i == 0
	vpxor		\c, \c, ymmword ptr [RCP + \rc]
.endif
	vmovdqa		LANE(\base, \i), \c
.else
	vpandn		T, \b1, \b2
	vpxor		T, T, \b0
	vmovdqa		LANE(\base, \i), T
	vpxor		\c, \c, T
.endif
.endm

/* chi over B0..B4 into row y of the state at out; iota on lane 0 with
 * the constant at [RCP + rc] if y = 0 */
.macro CHI_ROW out, y, rc=0
	CHI		C0, B0, B1, B2, \out, 5*\y + 0, \rc
	CHI		C1, B1, B2, B3, \out, 5*\y + 1, 0
	CHI		C2, B2, B3, B4, \out, 5*\y + 2, 0
	CHI		C3, B3, B4, B0, \out, 5*\y + 3, 0
	CHI		C4, B4, B0, B1, \out, 5*\y + 4, 0
.endm

/* one round from the state at in to out, iota constant at [RCP + rc];
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
	CHI_ROW		\out, 1
	THETA_RHO	B0, D1, \in, 1,  R1
	THETA_RHO	B1, D2, \in, 7,  R7
	THETA_RHO	B2, D3, \in, 13, R13
	THETA_RHO	B3, D4, \in, 19, R19
	THETA_RHO	B4, D0, \in, 20, R20
	CHI_ROW		\out, 2
	THETA_RHO	B0, D4, \in, 4,  R4
	THETA_RHO	B1, D0, \in, 5,  R5
	THETA_RHO	B2, D1, \in, 11, R11
	THETA_RHO	B3, D2, \in, 17, R17
	THETA_RHO	B4, D3, \in, 23, R23
	CHI_ROW		\out, 3
	THETA_RHO	B0, D2, \in, 2,  R2
	THETA_RHO	B1, D3, \in, 8,  R8
	THETA_RHO	B2, D4, \in, 14, R14
	THETA_RHO	B3, D0, \in, 15, R15
	THETA_RHO	B4, D1, \in, 21, R21
	CHI_ROW		\out, 4
.endm

/* round 0 lanes: data lane from memory, zero lane (B = rotl(D)), and
 * padding lane (B = rotl(K ^ D)) */
.macro RHO_ZERO b, d, rot
	vmovdqa		\b, \d
	ROL		\b, \rot, T
.endm
.macro RHO_PAD b, d, k, rot
	vpxor		\b, \d, ymmword ptr [rip + \k]
	ROL		\b, \rot, T
.endm

/* digest words in C0..C3 -> 4 x 32 bytes at [BOUT] */
.macro OUTPUT
	vpunpcklqdq	B0, C0, C1		/* n0, n2: w0 w1 */
	vpunpckhqdq	B1, C0, C1		/* n1, n3: w0 w1 */
	vpunpcklqdq	B2, C2, C3		/* n0, n2: w2 w3 */
	vpunpckhqdq	B3, C2, C3		/* n1, n3: w2 w3 */
	vperm2i128	C0, B0, B2, 0x20
	vperm2i128	C1, B1, B3, 0x20
	vperm2i128	C2, B0, B2, 0x31
	vperm2i128	C3, B1, B3, 0x31
	vmovdqu		ymmword ptr [BOUT + 0*32], C0
	vmovdqu		ymmword ptr [BOUT + 1*32], C1
	vmovdqu		ymmword ptr [BOUT + 2*32], C2
	vmovdqu		ymmword ptr [BOUT + 3*32], C3
.endm

.text
.p2align 6
/* one batch: 4 nodes at [BIN] -> 4 digests at [BOUT] */
.Lbatch:
	/* two 4x4 qword transposes: ymm0..7 = word 0..7 of nodes 0..3 */
	vmovdqu		ymm8,  ymmword ptr [BIN + 0*64]
	vmovdqu		ymm9,  ymmword ptr [BIN + 1*64]
	vmovdqu		ymm10, ymmword ptr [BIN + 2*64]
	vmovdqu		ymm11, ymmword ptr [BIN + 3*64]
	vpunpcklqdq	ymm12, ymm8, ymm9
	vpunpckhqdq	ymm13, ymm8, ymm9
	vpunpcklqdq	ymm14, ymm10, ymm11
	vpunpckhqdq	ymm15, ymm10, ymm11
	vperm2i128	ymm0, ymm12, ymm14, 0x20
	vperm2i128	ymm2, ymm12, ymm14, 0x31
	vperm2i128	ymm1, ymm13, ymm15, 0x20
	vperm2i128	ymm3, ymm13, ymm15, 0x31
	vmovdqu		ymm8,  ymmword ptr [BIN + 0*64 + 32]
	vmovdqu		ymm9,  ymmword ptr [BIN + 1*64 + 32]
	vmovdqu		ymm10, ymmword ptr [BIN + 2*64 + 32]
	vmovdqu		ymm11, ymmword ptr [BIN + 3*64 + 32]
	vpunpcklqdq	ymm12, ymm8, ymm9
	vpunpckhqdq	ymm13, ymm8, ymm9
	vpunpcklqdq	ymm14, ymm10, ymm11
	vpunpckhqdq	ymm15, ymm10, ymm11
	vperm2i128	ymm4, ymm12, ymm14, 0x20
	vperm2i128	ymm6, ymm12, ymm14, 0x31
	vperm2i128	ymm5, ymm13, ymm15, 0x20
	vperm2i128	ymm7, ymm13, ymm15, 0x31

	/* round 0: lanes 0..7 data, 8 = 0x01, 16 = 0x80..00, rest zero.
	 * The data lanes go to buffer 1 for the row loads below. */
	lea		BUF1, [BUF0 + 25*32]
	lea		RCP, [rip + .LRC4]
	vmovdqa		LANE(BUF1, 0), ymm0
	vmovdqa		LANE(BUF1, 1), ymm1
	vmovdqa		LANE(BUF1, 2), ymm2
	vmovdqa		LANE(BUF1, 3), ymm3
	vmovdqa		LANE(BUF1, 4), ymm4
	vmovdqa		LANE(BUF1, 5), ymm5
	vmovdqa		LANE(BUF1, 6), ymm6
	vmovdqa		LANE(BUF1, 7), ymm7
	vpxor		C0, ymm0, ymm5
	vpxor		C1, ymm1, ymm6
	vpxor		C1, C1, ymmword ptr [rip + .LK63]
	vpxor		C2, ymm2, ymm7
	vpxor		C3, ymm3, ymmword ptr [rip + .LK1]
	vmovdqa		C4, ymm4
	THETA
	THETA_RHO	B0, D0, BUF1, 0,  0
	THETA_RHO	B1, D1, BUF1, 6,  R6
	RHO_ZERO	B2, D2, R12
	RHO_ZERO	B3, D3, R18
	RHO_ZERO	B4, D4, R24
	CHI_ROW		BUF0, 0, 0
	THETA_RHO	B0, D3, BUF1, 3,  R3
	RHO_ZERO	B1, D4, R9
	RHO_ZERO	B2, D0, R10
	RHO_PAD		B3, D1, .LK63, R16
	RHO_ZERO	B4, D2, R22
	CHI_ROW		BUF0, 1
	THETA_RHO	B0, D1, BUF1, 1,  R1
	THETA_RHO	B1, D2, BUF1, 7,  R7
	RHO_ZERO	B2, D3, R13
	RHO_ZERO	B3, D4, R19
	RHO_ZERO	B4, D0, R20
	CHI_ROW		BUF0, 2
	THETA_RHO	B0, D4, BUF1, 4,  R4
	THETA_RHO	B1, D0, BUF1, 5,  R5
	RHO_ZERO	B2, D1, R11
	RHO_ZERO	B3, D2, R17
	RHO_ZERO	B4, D3, R23
	CHI_ROW		BUF0, 3
	THETA_RHO	B0, D2, BUF1, 2,  R2
	RHO_PAD		B1, D3, .LK1, R8
	RHO_ZERO	B2, D4, R14
	RHO_ZERO	B3, D0, R15
	RHO_ZERO	B4, D1, R21
	CHI_ROW		BUF0, 4

	/* rounds 1..22, two per iteration */
	mov		ecx, 11
1:
	ROUND		BUF0, BUF1, 32
	ROUND		BUF1, BUF0, 64
	add		RCP, 64
	dec		ecx
	jnz		1b

	/* round 23: theta, then row 0, x = 0..3 only */
	THETA
	THETA_RHO	B0, D0, BUF0, 0,  0
	THETA_RHO	B1, D1, BUF0, 6,  R6
	THETA_RHO	B2, D2, BUF0, 12, R12
	THETA_RHO	B3, D3, BUF0, 18, R18
	THETA_RHO	B4, D4, BUF0, 24, R24
	vpandn		C0, B1, B2
	vpxor		C0, C0, B0
	vpxor		C0, C0, ymmword ptr [RCP + 32]
	vpandn		C1, B2, B3
	vpxor		C1, C1, B1
	vpandn		C2, B3, B4
	vpxor		C2, C2, B2
	vpandn		C3, B4, B0
	vpxor		C3, C3, B3
	OUTPUT
	ret

	FUNCTION keccaktree_keccak256_avx2_x4

#ifdef _WIN64
.section .rdata,"dr"
#else
.section .rodata
#endif
.p2align 5
/* round constants, each broadcast to 4 lanes */
.LRC4:
	.irp rc, 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000, \
		 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009, \
		 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a, \
		 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003, \
		 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a, \
		 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
	.quad \rc, \rc, \rc, \rc
	.endr
.LK1:	.quad 1, 1, 1, 1
.LK63:	.quad 0x8000000000000000, 0x8000000000000000, 0x8000000000000000, 0x8000000000000000
/* vpshufb masks rotating each qword left by 8 and by 56 bits */
.LROT8:	.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
	.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
.LROT56: .byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8
	.byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
