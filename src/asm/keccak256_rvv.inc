/*
 * Keccak-f[1600] on a batch of vl nodes with the RISC-V vector extension
 * (RVV 1.0), for keccak256_rvv.S (plain V) and keccak256_rvv_zvkb.S (V with
 * the Zvkb rotate and ANDN).
 *
 * Vector-length agnostic: SEW = 64, LMUL = 1, so one vector register holds
 * one lane of VLEN/64 nodes (2 at VLEN = 128, 4 at 256, ...) and vsetvli
 * on the remaining count takes care of the tail. A segment load (vlseg8)
 * transposes 8-word nodes into lanes 0..7, a segment store (vsseg4) writes
 * lanes 0..3 back out as 32-byte digests.
 *
 * Registers: lane i in v<i> for the whole permutation (no renaming, the
 * round loop runs the same code 23 times), the column parities C0..C4 in
 * v25..v29 (free again after theta, then the chi products), v30/v31 the
 * rotation temporaries.
 *
 * Per round: theta 20 + 5 * (rotl + 1) + 25 XOR, rho+pi 24 rotl + 1 move,
 * chi 25 ANDN + 25 XOR, iota 1 XOR. That is 131 vector instructions with
 * Zvkb (rotl = VROR.VI, VANDN), and 214 without, where rotl takes VSLL,
 * VSRL, VOR (the 5-bit immediates only reach 31, so one shift of each pair
 * takes its count from a scalar register) and ANDN takes VNOT + VAND.
 *
 * The including file defines KECCAK_ZVKB for the Zvkb build.
 */

#define VC0	v25
#define VC1	v26
#define VC2	v27
#define VC3	v28
#define VC4	v29
#define VT0	v30
#define VT1	v31

/* dst = rotl(src, n), 0 < n < 64; tmp must differ from dst and src
 * (plain V only, clobbers t4) */
.macro VROTL dst, src, n, tmp
#ifdef KECCAK_ZVKB
	vror.vi		\dst, \src, 64 - \n
#else
.if \n < 32
	li		t4, 64 - \n
	vsll.vi		\tmp, \src, \n
	vsrl.vx		\dst, \src, t4
.else
	li		t4, \n
	vsll.vx		\tmp, \src, t4
	vsrl.vi		\dst, \src, 64 - \n
.endif
	vor.vv		\dst, \dst, \tmp
#endif
.endm

/* d = a & ~b; d must not be a (plain V) */
.macro VANDNOT d, a, b
#ifdef KECCAK_ZVKB
	vandn.vv	\d, \a, \b
#else
	vnot.v		\d, \b
	vand.vv		\d, \d, \a
#endif
.endm

/* the five lanes of a column ^= d */
.macro VXORCOL d, l0, l1, l2, l3, l4
	vxor.vv		\l0, \l0, \d
	vxor.vv		\l1, \l1, \d
	vxor.vv		\l2, \l2, \d
	vxor.vv		\l3, \l3, \d
	vxor.vv		\l4, \l4, \d
.endm

/* column parities C0..C4 */
.macro VTHETA_C
	vxor.vv		VC0, v0, v5
	vxor.vv		VC1, v1, v6
	vxor.vv		VC2, v2, v7
	vxor.vv		VC3, v3, v8
	vxor.vv		VC4, v4, v9
	vxor.vv		VC0, VC0, v10
	vxor.vv		VC1, VC1, v11
	vxor.vv		VC2, VC2, v12
	vxor.vv		VC3, VC3, v13
	vxor.vv		VC4, VC4, v14
	vxor.vv		VC0, VC0, v15
	vxor.vv		VC1, VC1, v16
	vxor.vv		VC2, VC2, v17
	vxor.vv		VC3, VC3, v18
	vxor.vv		VC4, VC4, v19
	vxor.vv		VC0, VC0, v20
	vxor.vv		VC1, VC1, v21
	vxor.vv		VC2, VC2, v22
	vxor.vv		VC3, VC3, v23
	vxor.vv		VC4, VC4, v24
.endm

/* d = cm ^ rotl(cp, 1): D[x] from C[x-1] (cm) and C[x+1] (cp) */
.macro VDVAL d, cp, cm, tmp
	VROTL		\d, \cp, 1, \tmp
	vxor.vv		\d, \d, \cm
.endm

/* theta: each D applied to its column right away; the destinations
 * alternate so consecutive D values do not wait on each other */
.macro VTHETA
	VTHETA_C
	VDVAL		VT0, VC1, VC4, VT1		/* D0 */
	VXORCOL		VT0, v0, v5, v10, v15, v20
	VDVAL		VT1, VC2, VC0, VT0		/* D1 */
	VXORCOL		VT1, v1, v6, v11, v16, v21
	VDVAL		VT0, VC3, VC1, VT1		/* D2 */
	VXORCOL		VT0, v2, v7, v12, v17, v22
	VDVAL		VT1, VC4, VC2, VT0		/* D3 */
	VXORCOL		VT1, v3, v8, v13, v18, v23
	VDVAL		VT0, VC0, VC3, VT1		/* D4 */
	VXORCOL		VT0, v4, v9, v14, v19, v24
.endm

/* rho and pi along the 24-cycle of pi, as in keccak256_rv64.inc: lane i
 * moves to lane y + 5*((2x + 3y) % 5) rotated by rho(i), walking the cycle
 * backwards so that only lane 1 needs a copy (in v25) */
.macro VRHO_PI
	vmv.v.v		v25, v1
	VROTL		v1, v6, 44, VT0
	VROTL		v6, v9, 20, VT1
	VROTL		v9, v22, 61, VT0
	VROTL		v22, v14, 39, VT1
	VROTL		v14, v20, 18, VT0
	VROTL		v20, v2, 62, VT1
	VROTL		v2, v12, 43, VT0
	VROTL		v12, v13, 25, VT1
	VROTL		v13, v19, 8, VT0
	VROTL		v19, v23, 56, VT1
	VROTL		v23, v15, 41, VT0
	VROTL		v15, v4, 27, VT1
	VROTL		v4, v24, 14, VT0
	VROTL		v24, v21, 2, VT1
	VROTL		v21, v8, 55, VT0
	VROTL		v8, v16, 45, VT1
	VROTL		v16, v5, 36, VT0
	VROTL		v5, v3, 28, VT1
	VROTL		v3, v18, 21, VT0
	VROTL		v18, v17, 15, VT1
	VROTL		v17, v11, 10, VT0
	VROTL		v11, v7, 6, VT1
	VROTL		v7, v10, 3, VT0
	VROTL		v10, v25, 1, VT1
.endm

/* chi on one row in place, the products for b0 and b1 set aside first
 * (they still need the old b0 and b1 for b3 and b4) */
.macro VCHI b0, b1, b2, b3, b4
	VANDNOT		v25, \b2, \b1
	VANDNOT		v26, \b3, \b2
	VANDNOT		v27, \b4, \b3
	VANDNOT		v28, \b0, \b4
	VANDNOT		v29, \b1, \b0
	vxor.vv		\b0, \b0, v25
	vxor.vv		\b1, \b1, v26
	vxor.vv		\b2, \b2, v27
	vxor.vv		\b3, \b3, v28
	vxor.vv		\b4, \b4, v29
.endm

/* one round, round constant in t3 */
.macro VROUND
	VTHETA
	VRHO_PI
	VCHI		v0, v1, v2, v3, v4
	vxor.vx		v0, v0, t3			/* iota */
	VCHI		v5, v6, v7, v8, v9
	VCHI		v10, v11, v12, v13, v14
	VCHI		v15, v16, v17, v18, v19
	VCHI		v20, v21, v22, v23, v24
.endm

/* round 23 (constant in t3): only row 0 of chi is needed for the digest,
 * from lanes 0, 6, 12, 18, 24 after theta and rho; the digest is left in
 * v0..v3 */
.macro VLAST_ROUND
	VTHETA_C
	VDVAL		VT0, VC1, VC4, VT1		/* D0 */
	vxor.vv		v0, v0, VT0
	VDVAL		VT1, VC2, VC0, VT0		/* D1 */
	vxor.vv		v6, v6, VT1
	VROTL		v1, v6, 44, VT0
	VDVAL		VT0, VC3, VC1, VT1		/* D2 */
	vxor.vv		v12, v12, VT0
	VROTL		v2, v12, 43, VT1
	VDVAL		VT1, VC4, VC2, VT0		/* D3 */
	vxor.vv		v18, v18, VT1
	VROTL		v3, v18, 21, VT0
	VDVAL		VT0, VC0, VC3, VT1		/* D4 */
	vxor.vv		v24, v24, VT0
	VROTL		v4, v24, 14, VT1
	VANDNOT		v25, v2, v1
	VANDNOT		v26, v3, v2
	VANDNOT		v27, v4, v3
	VANDNOT		v28, v0, v4
	vxor.vv		v0, v0, v25
	vxor.vv		v1, v1, v26
	vxor.vv		v2, v2, v27
	vxor.vv		v3, v3, v28
	vxor.vx		v0, v0, t3
.endm

/*
 * The kernel: a0 = output, a1 = input, a2 = nodes left.
 *	t0	vl, the nodes of this batch
 *	t1, t2	round constant pointer and its end (round 23)
 *	t3	round constant, t4 shift count, t5 = 1 << 63 (padding lane 16)
 *	a7	nonzero if input or output is not 8-byte aligned
 *
 * Misaligned buffers go through a 512-byte bounce buffer on the stack with
 * byte loads and stores (RVV may fault on misaligned 64-bit elements),
 * 8 nodes at a time so the buffer does not grow with VLEN.
 */
#define BOUNCE		512
#define BOUNCE_NODES	8

.macro KECCAK_RVV name
	FUNCTION	\name
	beqz		a2, 9f
	addi		sp, sp, -BOUNCE
	li		t5, 1
	slli		t5, t5, 63
	or		a7, a0, a1
	andi		a7, a7, 7
1:
	/* vl = min(nodes left, VLMAX), and at most BOUNCE_NODES if misaligned */
	mv		t3, a2
	beqz		a7, 2f
	li		t4, BOUNCE_NODES
	bleu		t3, t4, 2f
	mv		t3, t4
2:
	vsetvli		t0, t3, e64, m1, ta, ma
	bnez		a7, 3f
	vlseg8e64.v	v0, (a1)
	j		4f
3:
	slli		t3, t0, 6
	vsetvli		zero, t3, e8, m8, ta, ma
	vle8.v		v24, (a1)
	vse8.v		v24, (sp)
	vsetvli		zero, t0, e64, m1, ta, ma
	vlseg8e64.v	v0, (sp)
4:
	/* the padding lanes and the zero lanes */
	vmv.v.i		v8, 1
	vmv.v.i		v9, 0
	vmv.v.i		v10, 0
	vmv.v.i		v11, 0
	vmv.v.i		v12, 0
	vmv.v.i		v13, 0
	vmv.v.i		v14, 0
	vmv.v.i		v15, 0
	vmv.v.x		v16, t5
	vmv.v.i		v17, 0
	vmv.v.i		v18, 0
	vmv.v.i		v19, 0
	vmv.v.i		v20, 0
	vmv.v.i		v21, 0
	vmv.v.i		v22, 0
	vmv.v.i		v23, 0
	vmv.v.i		v24, 0

	lla		t1, .LRC
	addi		t2, t1, 8*23
5:
	ld		t3, 0(t1)
	VROUND
	addi		t1, t1, 8
	bne		t1, t2, 5b
	ld		t3, 0(t1)
	VLAST_ROUND

	bnez		a7, 6f
	vsseg4e64.v	v0, (a0)
	j		7f
6:
	vsseg4e64.v	v0, (sp)
	slli		t3, t0, 5
	vsetvli		zero, t3, e8, m4, ta, ma
	vle8.v		v24, (sp)
	vse8.v		v24, (a0)
7:
	slli		t3, t0, 6
	add		a1, a1, t3
	slli		t3, t0, 5
	add		a0, a0, t3
	sub		a2, a2, t0
	bnez		a2, 1b
	addi		sp, sp, BOUNCE
9:
	ret
	END_FUNCTION	\name
.endm
