/*
 * Keccak-f[1600] on one node in the RV64 general registers, for
 * keccak256_rv64_x1.S (base RV64I) and keccak256_zbb_x1.S (Zbb).
 *
 * The 25 lanes live in fixed registers for the whole permutation (no
 * renaming, every round is the same code), which takes 25 of the 28
 * allocatable registers; t0..t2 are the temporaries:
 *
 *	A0..A7		a0..a7		(the input words, loaded straight in)
 *	A8, A9		s0, s1
 *	A10..A19	s2..s11
 *	A20..A23	t3..t6
 *	A24		ra
 *
 * so output, input and count are kept on the stack, and so are the column
 * parities C0..C3 (C4 stays in t2) while theta forms the D values.
 *
 * Per round:
 *	theta	20 XOR for the parities, then D[x] = C[x-1] ^ rotl(C[x+1], 1)
 *		applied to one column at a time (5 rotl, 5 + 25 XOR, 8 loads,
 *		4 stores)
 *	rho+pi	one chain along the 24-cycle of pi: each lane is rotated
 *		straight into the register of its destination, whose old
 *		value has already moved on (24 rotl, 1 MV)
 *	chi	in place per row: the two products that need b0 and b1 are
 *		set aside first, so no row needs a copy (25 ANDNOT, 25 XOR)
 *	iota	1 load (AUIPC + LD), 1 XOR
 * With Zbb that is 145 instructions (rotl = RORI, ANDNOT native); base RV64I
 * spends 3 instructions per rotation and 2 per ANDNOT, 228 in all.
 *
 * The including file defines KECCAK_ZBB for the Zbb build.
 */

#define A0	a0
#define A1	a1
#define A2	a2
#define A3	a3
#define A4	a4
#define A5	a5
#define A6	a6
#define A7	a7
#define A8	s0
#define A9	s1
#define A10	s2
#define A11	s3
#define A12	s4
#define A13	s5
#define A14	s6
#define A15	s7
#define A16	s8
#define A17	s9
#define A18	s10
#define A19	s11
#define A20	t3
#define A21	t4
#define A22	t5
#define A23	t6
#define A24	ra

/*
 * Stack frame of the kernel (FRAME bytes):
 *	0..63		bounce buffer for misaligned input/output
 *	OUT, IN, CNT	output and input pointers, nodes left
 *	C0..C3		column parities
 *	SAVE..		ra, s0..s11
 */
#define BUF	0
#define OUT	64
#define IN	72
#define CNT	80
#define C0	88
#define C1	96
#define C2	104
#define C3	112
#define SAVE	120
#define FRAME	224

/* dst = rotl(src, n), 0 < n < 64; tmp is scratch (base RV64I only) */
.macro ROTL dst, src, n, tmp
#ifdef KECCAK_ZBB
	rori		\dst, \src, 64 - \n
#else
	slli		\tmp, \src, \n
	srli		\dst, \src, 64 - \n
	or		\dst, \dst, \tmp
#endif
.endm

/* d = a & ~b; d must not be a (base RV64I) */
.macro ANDNOT d, a, b
#ifdef KECCAK_ZBB
	andn		\d, \a, \b
#else
	not		\d, \b
	and		\d, \d, \a
#endif
.endm

/* the five lanes of a column ^= d */
.macro XORCOL d, l0, l1, l2, l3, l4
	xor		\l0, \l0, \d
	xor		\l1, \l1, \d
	xor		\l2, \l2, \d
	xor		\l3, \l3, \d
	xor		\l4, \l4, \d
.endm

/* column parities: C0..C3 to the stack, C4 in t2 (two and three chains
 * interleaved for the dual-issue in-order cores) */
.macro THETA_C
	xor		t0, A0, A5
	xor		t1, A1, A6
	xor		t0, t0, A10
	xor		t1, t1, A11
	xor		t0, t0, A15
	xor		t1, t1, A16
	xor		t0, t0, A20
	xor		t1, t1, A21
	sd		t0, C0(sp)
	sd		t1, C1(sp)
	xor		t0, A2, A7
	xor		t1, A3, A8
	xor		t2, A4, A9
	xor		t0, t0, A12
	xor		t1, t1, A13
	xor		t2, t2, A14
	xor		t0, t0, A17
	xor		t1, t1, A18
	xor		t2, t2, A19
	xor		t0, t0, A22
	xor		t1, t1, A23
	xor		t2, t2, A24
	sd		t0, C2(sp)
	sd		t1, C3(sp)
.endm

/* d = cm ^ rotl(cp, 1) in cp's register: D[x] from C[x-1] (cm) and
 * C[x+1] (cp) */
.macro DVAL cp, cm
	ROTL		\cp, \cp, 1, t1
	xor		\cp, \cp, \cm
.endm

/* theta: D0, D3, D2, D4, D1 in turn, each applied to its column right away */
.macro THETA
	THETA_C
	ld		t0, C1(sp)
	DVAL		t0, t2				/* D0 = C4 ^ rotl(C1) */
	XORCOL		t0, A0, A5, A10, A15, A20
	ld		t0, C2(sp)
	DVAL		t2, t0				/* D3 = C2 ^ rotl(C4) */
	XORCOL		t2, A3, A8, A13, A18, A23
	ld		t2, C3(sp)
	ld		t0, C1(sp)
	DVAL		t2, t0				/* D2 = C1 ^ rotl(C3) */
	XORCOL		t2, A2, A7, A12, A17, A22
	ld		t2, C0(sp)
	ld		t0, C3(sp)
	DVAL		t2, t0				/* D4 = C3 ^ rotl(C0) */
	XORCOL		t2, A4, A9, A14, A19, A24
	ld		t2, C2(sp)
	ld		t0, C0(sp)
	DVAL		t2, t0				/* D1 = C0 ^ rotl(C2) */
	XORCOL		t2, A1, A6, A11, A16, A21
.endm

/* rho and pi: lane i moves to lane pi(i) = y + 5*((2x + 3y) % 5) rotated by
 * rho(i). Walking the cycle backwards (1 <- 6 <- 9 <- ... <- 10 <- 1),
 * every destination's old value has already moved on when it is written,
 * so only lane 1 needs a copy. The temporaries alternate so the base
 * build's shift pairs can overlap. */
.macro RHO_PI
	mv		t0, A1
	ROTL		A1, A6, 44, t1
	ROTL		A6, A9, 20, t2
	ROTL		A9, A22, 61, t1
	ROTL		A22, A14, 39, t2
	ROTL		A14, A20, 18, t1
	ROTL		A20, A2, 62, t2
	ROTL		A2, A12, 43, t1
	ROTL		A12, A13, 25, t2
	ROTL		A13, A19, 8, t1
	ROTL		A19, A23, 56, t2
	ROTL		A23, A15, 41, t1
	ROTL		A15, A4, 27, t2
	ROTL		A4, A24, 14, t1
	ROTL		A24, A21, 2, t2
	ROTL		A21, A8, 55, t1
	ROTL		A8, A16, 45, t2
	ROTL		A16, A5, 36, t1
	ROTL		A5, A3, 28, t2
	ROTL		A3, A18, 21, t1
	ROTL		A18, A17, 15, t2
	ROTL		A17, A11, 10, t1
	ROTL		A11, A7, 6, t2
	ROTL		A7, A10, 3, t1
	ROTL		A10, t0, 1, t2
.endm

/* chi on one row in place: b[x] ^= ~b[x+1] & b[x+2]. The products for
 * b0 and b1 go to t0 and t1 first, as b0 and b1 are still needed by the
 * products of b3 and b4. With r given (row 0), iota adds round constant r
 * to b0, loaded as soon as t2 is free. */
.macro CHI b0, b1, b2, b3, b4, r
	ANDNOT		t0, \b2, \b1
	ANDNOT		t1, \b3, \b2
	ANDNOT		t2, \b4, \b3
	xor		\b2, \b2, t2
	ANDNOT		t2, \b0, \b4
	xor		\b3, \b3, t2
	ANDNOT		t2, \b1, \b0
	xor		\b4, \b4, t2
.ifnb \r
	ld		t2, .LRC + 8*\r
.endif
	xor		\b0, \b0, t0
	xor		\b1, \b1, t1
.ifnb \r
	xor		\b0, \b0, t2
.endif
.endm

/* rounds 0..22 */
.macro ROUND r
	THETA
	RHO_PI
	CHI		A0, A1, A2, A3, A4, \r		/* and iota */
	CHI		A5, A6, A7, A8, A9
	CHI		A10, A11, A12, A13, A14
	CHI		A15, A16, A17, A18, A19
	CHI		A20, A21, A22, A23, A24
.endm

/* round 23: only lanes 0..3 of the result are needed, i.e. row 0 of chi,
 * whose inputs are lanes 0, 6, 12, 18, 24 after theta and rho. Each D is
 * applied to its one lane, rotated into lanes 0..4, and the digest is left
 * in A0..A3. */
.macro LAST_ROUND
	THETA_C
	ld		t0, C1(sp)
	DVAL		t0, t2				/* D0 = C4 ^ rotl(C1) */
	xor		A0, A0, t0
	ld		t0, C2(sp)
	DVAL		t2, t0				/* D3 = C2 ^ rotl(C4) */
	xor		t2, t2, A18
	ROTL		A3, t2, 21, t1
	ld		t2, C3(sp)
	ld		t0, C1(sp)
	DVAL		t2, t0				/* D2 = C1 ^ rotl(C3) */
	xor		t2, t2, A12
	ROTL		A2, t2, 43, t1
	ld		t2, C0(sp)
	ld		t0, C3(sp)
	DVAL		t2, t0				/* D4 = C3 ^ rotl(C0) */
	xor		t2, t2, A24
	ROTL		A4, t2, 14, t1
	ld		t2, C2(sp)
	ld		t0, C0(sp)
	DVAL		t2, t0				/* D1 = C0 ^ rotl(C2) */
	xor		t2, t2, A6
	ROTL		A1, t2, 44, t1
	ANDNOT		t0, A2, A1
	ANDNOT		t1, A3, A2
	ANDNOT		t2, A4, A3
	xor		A2, A2, t2
	ANDNOT		t2, A0, A4
	xor		A3, A3, t2
	xor		A1, A1, t1
	ld		t1, .LRC + 8*23
	xor		A0, A0, t0
	xor		A0, A0, t1
.endm

/* the 64-byte node at [base] into lanes 0..7 and the padding lanes
 * (0x01 after the message in lane 8, 0x80 in the last byte of the rate,
 * lane 16), the other lanes zero */
.macro LOAD_STATE base
	ld		A1, 8(\base)
	ld		A2, 16(\base)
	ld		A3, 24(\base)
	ld		A4, 32(\base)
	ld		A5, 40(\base)
	ld		A6, 48(\base)
	ld		A7, 56(\base)
	ld		A0, 0(\base)
	li		A8, 1
	li		A16, 1
	slli		A16, A16, 63
	li		A9, 0
	li		A10, 0
	li		A11, 0
	li		A12, 0
	li		A13, 0
	li		A14, 0
	li		A15, 0
	li		A17, 0
	li		A18, 0
	li		A19, 0
	li		A20, 0
	li		A21, 0
	li		A22, 0
	li		A23, 0
	li		A24, 0
.endm

/* n bytes from [src] to [dst], one at a time (for misaligned buffers:
 * misaligned LD/SD may trap into slow kernel emulation, or fault) */
.macro COPY_BYTES dst, src, n, tmp, cnt
	li		\cnt, \n
71:
	lbu		\tmp, 0(\src)
	sb		\tmp, 0(\dst)
	addi		\src, \src, 1
	addi		\dst, \dst, 1
	addi		\cnt, \cnt, -1
	bnez		\cnt, 71b
.endm

/* the kernel body (KECCAK_X1 below) */

.macro KECCAK_X1 name
	FUNCTION	\name
	beqz		a2, 3f
	addi		sp, sp, -FRAME
	sd		ra, SAVE + 0(sp)
	sd		s0, SAVE + 8(sp)
	sd		s1, SAVE + 16(sp)
	sd		s2, SAVE + 24(sp)
	sd		s3, SAVE + 32(sp)
	sd		s4, SAVE + 40(sp)
	sd		s5, SAVE + 48(sp)
	sd		s6, SAVE + 56(sp)
	sd		s7, SAVE + 64(sp)
	sd		s8, SAVE + 72(sp)
	sd		s9, SAVE + 80(sp)
	sd		s10, SAVE + 88(sp)
	sd		s11, SAVE + 96(sp)
	sd		a0, OUT(sp)
	sd		a1, IN(sp)
	sd		a2, CNT(sp)
1:
	/* load the next node, through the bounce buffer if misaligned */
	ld		t0, IN(sp)
	addi		t1, t0, 64
	sd		t1, IN(sp)
	andi		t1, t0, 7
	beqz		t1, 2f
	addi		t1, sp, BUF
	COPY_BYTES	t1, t0, 64, t2, a7
	addi		t0, sp, BUF
2:
	LOAD_STATE	t0
	.irp r, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22
	ROUND		\r
	.endr
	LAST_ROUND
	/* store the digest, through the bounce buffer if misaligned */
	ld		t0, OUT(sp)
	addi		t1, t0, 32
	sd		t1, OUT(sp)
	andi		t1, t0, 7
	bnez		t1, 4f
	sd		A0, 0(t0)
	sd		A1, 8(t0)
	sd		A2, 16(t0)
	sd		A3, 24(t0)
	j		5f
4:
	sd		A0, BUF + 0(sp)
	sd		A1, BUF + 8(sp)
	sd		A2, BUF + 16(sp)
	sd		A3, BUF + 24(sp)
	addi		t1, sp, BUF
	COPY_BYTES	t0, t1, 32, t2, a7
5:
	ld		t0, CNT(sp)
	addi		t0, t0, -1
	sd		t0, CNT(sp)
	bnez		t0, 1b

	ld		ra, SAVE + 0(sp)
	ld		s0, SAVE + 8(sp)
	ld		s1, SAVE + 16(sp)
	ld		s2, SAVE + 24(sp)
	ld		s3, SAVE + 32(sp)
	ld		s4, SAVE + 40(sp)
	ld		s5, SAVE + 48(sp)
	ld		s6, SAVE + 56(sp)
	ld		s7, SAVE + 64(sp)
	ld		s8, SAVE + 72(sp)
	ld		s9, SAVE + 80(sp)
	ld		s10, SAVE + 88(sp)
	ld		s11, SAVE + 96(sp)
	addi		sp, sp, FRAME
3:
	ret
	END_FUNCTION	\name
.endm
