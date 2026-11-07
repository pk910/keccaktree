/*
 * Rounds of the ARMv8.0 Advanced SIMD kernels (keccak256_neon_x2.S,
 * keccak256_neon_x3.S), two nodes per vector register as in
 * keccak256_neon.inc. Without FEAT_SHA3 a rotation is SHL + SRI into a
 * fresh register and chi is BIC + EOR: 157 vector instructions per round.
 *
 * Neoverse N1 (and Cortex-A76/A77/A78) run the vector shifts on one of
 * their two vector pipes only and hand each instruction to a pipe when it
 * is dispatched, so a run of shifts leaves the other pipe idle: ten shifts
 * in a row (the rho of one row) measured 10% slower than the three-per-lane
 * pattern, and spreading them further is what this round is built around.
 *
 * 1. Every shift that can be a plain ALU instruction is one: the left
 *    shift by one of theta's rotl(C, 1) and of lane 1's rho is an ADD
 *    (+1.8% on N1), and the two lanes whose rho rotation is a multiple of
 *    8 (lanes 19 and 23) rotate with one TBL (+4%). Spending an extra
 *    instruction to avoid a shift (ADD, ADD, SRI for lane 21) does not pay.
 *
 * 2. The chi of each row is interleaved with the rho of the next row
 *    (PAIR), two chi instructions between the rotations, so the shift pipe
 *    sees at most two shifts in five instructions. That needs three free
 *    registers while the rows run (two for a row's first chi outputs, one
 *    for the next row's rho, which rotates each lane into the register the
 *    previous lane vacated) and the register file has two, so lane 2, which
 *    only row 4 reads, spends the rows on the stack (one STR and one LDR
 *    per round on the idle load/store pipes). Row 4 then rotates into the
 *    theta registers D0..D4, dead once its five EORs are done, so its rho
 *    pairs with the chi of row 3 without a free register at all.
 *
 * The register of every lane and of D0..D4 therefore changes from round to
 * round: each ROUND line names the 25 lane registers, the five D registers
 * and the free pair, following the flow in the comment above V_THETA.
 * Round 0 only has lanes 0..7 (input), 8 (0x01) and 16 (0x80..0) non-zero,
 * so its parities are 3 instructions and the zero lanes just rotate D.
 * Round 23 computes only the four output lanes.
 *
 * The including file defines VSPILL, the stack offset of the 16-byte slot
 * for lane 2.
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

/* b = rotl(a, n), b != a: SHL + SRI, ADD + SRI for n = 1, and for n = 8
 * and 56 a byte permutation (TBL, its index vector loaded into b itself) */
.macro ROT b, a, n
.if \n == 8 || \n == 56
	ldr		q\b, .LTBL\n
	tbl		v\b\().16b, {v\a\().16b}, v\b\().16b
.elseif \n == 1
	add		v\b\().2d, v\a\().2d, v\a\().2d
	sri		v\b\().2d, v\a\().2d, #63
.elseif \n
	shl		v\b\().2d, v\a\().2d, #\n
	sri		v\b\().2d, v\a\().2d, #(64 - \n)
.else
	.error "ROT by 0"
.endif
.endm

/* b = rotl(a ^ d, n), a is left with a ^ d (or holds the result, n = 0) */
.macro RHO b, a, d, n
.if \n
	eor		v\a\().16b, v\a\().16b, v\d\().16b
	ROT		\b, \a, \n
.else
	eor		v\b\().16b, v\a\().16b, v\d\().16b
.endif
.endm

/* b = rotl(d, n), for a zero lane in round 0 */
.macro RHO_ZERO b, d, n
	shl		v\b\().2d, v\d\().2d, #\n
	sri		v\b\().2d, v\d\().2d, #(64 - \n)
.endm

/* chi on a row: out[x] = b[x] ^ (~b[x+1] & b[x+2]) with out0..4 -> f0, f1,
 * b2, b0, b1 (b3, b4 freed). Outputs 3 and 4 are built in place: each
 * input's last use is the BIC that starts the output taking its place.
 * In five pieces of two instructions for the interleaving. */
.macro CHI_1 b0, b1, b2, b3, b4, f0, f1
	bic		v\f1\().16b, v\b2\().16b, v\b1\().16b
	eor		v\f0\().16b, v\b0\().16b, v\f1\().16b
.endm
.macro CHI_2 b0, b1, b2, b3, b4, f0, f1
	bic		v\f1\().16b, v\b3\().16b, v\b2\().16b
	eor		v\f1\().16b, v\b1\().16b, v\f1\().16b
.endm
.macro CHI_3 b0, b1, b2, b3, b4, f0, f1
	bic		v\b1\().16b, v\b1\().16b, v\b0\().16b
	bic		v\b0\().16b, v\b0\().16b, v\b4\().16b
.endm
.macro CHI_4 b0, b1, b2, b3, b4, f0, f1
	eor		v\b0\().16b, v\b3\().16b, v\b0\().16b
	eor		v\b1\().16b, v\b4\().16b, v\b1\().16b
.endm
.macro CHI_5 b0, b1, b2, b3, b4, f0, f1
	bic		v\b3\().16b, v\b4\().16b, v\b3\().16b
	eor		v\b2\().16b, v\b2\().16b, v\b3\().16b
.endm
.macro CHI_ROW b0, b1, b2, b3, b4, f0, f1
	CHI_1		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	CHI_2		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	CHI_3		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	CHI_4		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	CHI_5		\b0, \b1, \b2, \b3, \b4, \f0, \f1
.endm

/* rho on a row with one free register t: the lanes end in t, a0, a1, a2,
 * a3 and a4 is freed */
.macro RHO_ROW a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, t
	RHO		\t, \a0, \d0, \r0
	RHO		\a0, \a1, \d1, \r1
	RHO		\a1, \a2, \d2, \r2
	RHO		\a2, \a3, \d3, \r3
	RHO		\a3, \a4, \d4, \r4
.endm

/* chi of a row (b0..b4, outputs 0 and 1 into f0, f1) interleaved with the
 * rho of the next row (RHO_ROW's arguments) */
.macro PAIR b0, b1, b2, b3, b4, f0, f1, a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4, t
	eor		v\a0\().16b, v\a0\().16b, v\d0\().16b
	eor		v\a1\().16b, v\a1\().16b, v\d1\().16b
	CHI_1		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\t, \a0, \r0
	eor		v\a2\().16b, v\a2\().16b, v\d2\().16b
	CHI_2		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\a0, \a1, \r1
	eor		v\a3\().16b, v\a3\().16b, v\d3\().16b
	CHI_3		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\a1, \a2, \r2
	eor		v\a4\().16b, v\a4\().16b, v\d4\().16b
	CHI_4		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\a2, \a3, \r3
	CHI_5		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\a3, \a4, \r4
.endm

/* the same with the rho of row 4, which rotates each lane into the D
 * register it was just EORed with (all five EORs first) */
.macro PAIR4 b0, b1, b2, b3, b4, f0, f1, a0, a1, a2, a3, a4, d0, d1, d2, d3, d4, r0, r1, r2, r3, r4
	eor		v\a0\().16b, v\a0\().16b, v\d0\().16b
	eor		v\a1\().16b, v\a1\().16b, v\d1\().16b
	eor		v\a2\().16b, v\a2\().16b, v\d2\().16b
	eor		v\a3\().16b, v\a3\().16b, v\d3\().16b
	eor		v\a4\().16b, v\a4\().16b, v\d4\().16b
	CHI_1		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\d0, \a0, \r0
	CHI_2		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\d1, \a1, \r1
	CHI_3		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\d2, \a2, \r2
	CHI_4		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\d3, \a3, \r3
	CHI_5		\b0, \b1, \b2, \b3, \b4, \f0, \f1
	ROT		\d4, \a4, \r4
.endm

#define VARGS a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, d0, d1, d2, d3, d4, p, q
#define VPASS \a0, \a1, \a2, \a3, \a4, \a5, \a6, \a7, \a8, \a9, \a10, \a11, \a12, \a13, \a14, \a15, \a16, \a17, \a18, \a19, \a20, \a21, \a22, \a23, \a24, \d0, \d1, \d2, \d3, \d4, \p, \q

/* The pieces of a round, in order. Row y takes B[x] from lane
 * ((x+3y)%5) + 5x and D[(x+3y)%5]. The free registers along the way:
 *   after theta         p, q, a2 (on the stack)
 *   row 0 in p, a0, a6, a12, a18  free q, a2, a24
 *   chi 0 -> q, a2, a6, p, a0; frees a12, a18 | row 1 in a24, a3, a9, a10, a16
 *   chi 1 -> a12, a18, a9, a24, a3; frees a10, a16 | row 2 in a22, a1, a7, a13, a19
 *   chi 2 -> a10, a16, a7, a22, a1; frees a13, a19 | row 3 in a20, a4, a5, a11, a17
 *   lane 2 reloaded into a23
 *   chi 3 -> a13, a19, a5, a20, a4; frees a11, a17 | row 4 in d2, d3, d4, d0, d1
 *   chi 4 -> a11, a17, d4, d2, d3; frees d0, d1; round constant through a23
 * so the next round's lanes are q, a2, a6, p, a0, a12, a18, a9, a24, a3,
 * a10, a16, a7, a22, a1, a13, a19, a5, a20, a4, a11, a17, d4, d2, d3 and
 * its D registers and free pair come from a8, a14, a15, a21, a23, d0, d1.
 * The parities of columns 2 and 1 are last (lane 2 goes to the stack as
 * soon as it is read). */
.macro V_THETA VARGS
	PARITY		\d1, \a0, \a5, \a10, \a15, \a20
	PARITY		\d3, \a2, \a7, \a12, \a17, \a22
	str		q\a2, [sp, #VSPILL]
	PARITY		\d4, \a3, \a8, \a13, \a18, \a23
	PARITY		\p, \a4, \a9, \a14, \a19, \a24
	PARITY		\d2, \a1, \a6, \a11, \a16, \a21
	THETA_D		\d0, \p, \d2, \q
	THETA_D		\d2, \d2, \d4, \q
	THETA_D		\d4, \d4, \d1, \q
	THETA_D		\d1, \d1, \d3, \q
	THETA_D		\d3, \d3, \p, \q
.endm
.macro V_RHO0 VARGS
	RHO_ROW		\a0, \a6, \a12, \a18, \a24, \d0, \d1, \d2, \d3, \d4, 0, 44, 43, 21, 14, \p
.endm
.macro V_PAIR01 VARGS
	PAIR		\p, \a0, \a6, \a12, \a18, \q, \a2, \a3, \a9, \a10, \a16, \a22, \d3, \d4, \d0, \d1, \d2, 28, 20, 3, 45, 61, \a24
.endm
.macro V_PAIR12 VARGS
	PAIR		\a24, \a3, \a9, \a10, \a16, \a12, \a18, \a1, \a7, \a13, \a19, \a20, \d1, \d2, \d3, \d4, \d0, 1, 6, 25, 8, 18, \a22
.endm
.macro V_PAIR23 VARGS
	PAIR		\a22, \a1, \a7, \a13, \a19, \a10, \a16, \a4, \a5, \a11, \a17, \a23, \d4, \d0, \d1, \d2, \d3, 27, 36, 10, 15, 56, \a20
.endm
.macro V_PAIR34 VARGS
	ldr		q\a23, [sp, #VSPILL]
	PAIR4		\a20, \a4, \a5, \a11, \a17, \a13, \a19, \a23, \a8, \a14, \a15, \a21, \d2, \d3, \d4, \d0, \d1, 62, 55, 39, 41, 2
.endm
.macro V_CHI4 r, VARGS
	ldr		q\a23, .LRC + 16*\r
	CHI_ROW		\d2, \d3, \d4, \d0, \d1, \a11, \a17
	eor		v\q\().16b, v\q\().16b, v\a23\().16b
.endm

.macro ROUND r, VARGS
	V_THETA		VPASS
	V_RHO0		VPASS
	V_PAIR01	VPASS
	V_PAIR12	VPASS
	V_PAIR23	VPASS
	V_PAIR34	VPASS
	V_CHI4		\r, VPASS
.endm

/* round 0 on the state lane i = v(i): input words in v0..v7, 0x01 in v8,
 * 0x80..0 in v16, the rest zero (not initialised; RHO_ZERO ignores them);
 * D0..D4 in v25..v29, free pair v30, v31; rho into the free pair and the
 * first three lanes of the row, chi into the last two and in place. In two
 * halves: theta with rows 0..1, then rows 2..4. */
.macro FIRST_ROUND_A
	eor		v26.16b, v0.16b, v5.16b
	XOR3		27, 1, 6, 16
	eor		v28.16b, v2.16b, v7.16b
	eor		v29.16b, v3.16b, v8.16b
	mov		v30.16b, v4.16b
	THETA_D		25, 30, 27, 31
	THETA_D		27, 27, 29, 31
	THETA_D		29, 29, 26, 31
	THETA_D		26, 26, 28, 31
	THETA_D		28, 28, 30, 31
	RHO		30, 0, 25, 0
	RHO		31, 6, 26, 44
	RHO_ZERO	0, 27, 43
	RHO_ZERO	6, 28, 21
	RHO_ZERO	12, 29, 14
	CHI_ROW		30, 31, 0, 6, 12, 18, 24
	RHO		6, 3, 28, 28
	RHO_ZERO	12, 29, 20
	RHO_ZERO	3, 25, 3
	RHO		9, 16, 26, 45
	RHO_ZERO	10, 27, 61
	CHI_ROW		6, 12, 3, 9, 10, 16, 22
.endm
.macro FIRST_ROUND_B
	RHO		9, 1, 26, 1
	RHO		10, 7, 27, 6
	RHO_ZERO	1, 28, 25
	RHO_ZERO	7, 29, 8
	RHO_ZERO	13, 25, 18
	CHI_ROW		9, 10, 1, 7, 13, 19, 20
	RHO		7, 4, 29, 27
	RHO		13, 5, 25, 36
	RHO_ZERO	4, 26, 10
	RHO_ZERO	5, 27, 15
	RHO_ZERO	11, 28, 56
	CHI_ROW		7, 13, 4, 5, 11, 17, 23
	RHO		5, 2, 27, 62
	RHO		11, 8, 28, 55
	RHO_ZERO	2, 29, 39
	RHO_ZERO	8, 25, 41
	RHO_ZERO	14, 26, 2
	ldr		q25, .LRC
	CHI_ROW		5, 11, 2, 8, 14, 15, 21
	eor		v18.16b, v18.16b, v25.16b
.endm
.macro FIRST_ROUND
	FIRST_ROUND_A
	FIRST_ROUND_B
.endm

/* round 23: theta without the spill (every lane but row 0's is dead after
 * the parities), row 0 in p, a0, a6, a12, a18, chi outputs 0..3 into
 * o0..o3 (dead lanes outside v25..v28) and from there zipped into v25,
 * v26 (node 0) and v27, v28 (node 1), ready to store. */
.macro V_THETA_LAST VARGS
	PARITY		\d1, \a0, \a5, \a10, \a15, \a20
	PARITY		\d2, \a1, \a6, \a11, \a16, \a21
	PARITY		\d3, \a2, \a7, \a12, \a17, \a22
	PARITY		\d4, \a3, \a8, \a13, \a18, \a23
	PARITY		\p, \a4, \a9, \a14, \a19, \a24
	THETA_D		\d0, \p, \d2, \q
	THETA_D		\d2, \d2, \d4, \q
	THETA_D		\d4, \d4, \d1, \q
	THETA_D		\d1, \d1, \d3, \q
	THETA_D		\d3, \d3, \p, \q
.endm
.macro V_LAST_ROW o0, o1, o2, o3, VARGS
	V_RHO0		VPASS
	ldr		q\a2, .LRC + 16*23
	bic		v\o0\().16b, v\a6\().16b, v\a0\().16b
	eor		v\o0\().16b, v\p\().16b, v\o0\().16b
	bic		v\o1\().16b, v\a12\().16b, v\a6\().16b
	eor		v\o1\().16b, v\a0\().16b, v\o1\().16b
	bic		v\o2\().16b, v\a18\().16b, v\a12\().16b
	eor		v\o2\().16b, v\a6\().16b, v\o2\().16b
	bic		v\o3\().16b, v\p\().16b, v\a18\().16b
	eor		v\o3\().16b, v\a12\().16b, v\o3\().16b
	eor		v\o0\().16b, v\o0\().16b, v\a2\().16b
	zip1		v25.2d, v\o0\().2d, v\o1\().2d
	zip1		v26.2d, v\o2\().2d, v\o3\().2d
	zip2		v27.2d, v\o0\().2d, v\o1\().2d
	zip2		v28.2d, v\o2\().2d, v\o3\().2d
.endm
.macro LAST_ROUND o0, o1, o2, o3, VARGS
	V_THETA_LAST	VPASS
	V_LAST_ROW	\o0, \o1, \o2, \o3, VPASS
.endm

/* TBL indices of the byte rotations: rotl by 8 and by 56 in each 64-bit
 * lane (after KECCAK_RC, which the kernels place after their code) */
.macro ASIMD_TABLES
.p2align 4
.LTBL8:	.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
.LTBL56:	.byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8
.endm
