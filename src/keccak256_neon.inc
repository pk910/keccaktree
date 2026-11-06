/*
 * Shared by the AArch64 vector kernels keccak256_sha3_x2.S (FEAT_SHA3,
 * rounds in keccak256_sha3.inc), keccak256_neon_x2.S (ARMv8.0 Advanced
 * SIMD, rounds in that file) and keccak256_sha3_x3.S: Keccak-f[1600] on two
 * nodes, one per 64-bit lane of the vector registers.
 *
 * The 25 lanes stay in registers for the whole permutation. Instead of the
 * pi moves, every round takes the register of each lane as an argument
 * (the ROUND lines in the kernels): chi writes two lanes into the free pair
 * and the rest over their inputs, and the next round's line names the new
 * places. Theta keeps D[0..4] in v25..v29; C[0..4] use them and the free
 * pair p, q before D exists:
 *
 *   C0 C1 C2 C3 C4  in  v26 v27 v28 v29 p
 *   D0 = C4 ^ rotl(C1)  -> v25        D2 = C1 ^ rotl(C3)  -> v27
 *   D4 = C3 ^ rotl(C0)  -> v29        D1 = C0 ^ rotl(C2)  -> v26
 *   D3 = C2 ^ rotl(C4)  -> v28        free: p, q
 *
 * The including file defines PARITY c, a0..a4 (c = a0 ^ .. ^ a4) and
 * THETA_D d, c1, c2, t (d = c1 ^ rotl(c2, 1), t scratch). All macro
 * arguments are register numbers.
 *
 * Round 0 only has lanes 0..7 (input), 8 (0x01) and 16 (0x80..0) non-zero,
 * so its parities are 3 instructions and the zero lanes just rotate D.
 * Round 23 computes only the four output lanes.
 */
#define D0 25
#define D1 26
#define D2 27
#define D3 28
#define D4 29

#define ARGS a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, p, q
#define PASS \a0, \a1, \a2, \a3, \a4, \a5, \a6, \a7, \a8, \a9, \a10, \a11, \a12, \a13, \a14, \a15, \a16, \a17, \a18, \a19, \a20, \a21, \a22, \a23, \a24, \p, \q

/* theta: D0..D4 from the state in a0..a24; p, q free */
.macro THETA ARGS
	PARITY		D1, \a0, \a5, \a10, \a15, \a20
	PARITY		D2, \a1, \a6, \a11, \a16, \a21
	PARITY		D3, \a2, \a7, \a12, \a17, \a22
	PARITY		D4, \a3, \a8, \a13, \a18, \a23
	PARITY		\p, \a4, \a9, \a14, \a19, \a24
	THETA_D		D0, \p, D2, \q
	THETA_D		D2, D2, D4, \q
	THETA_D		D4, D4, D1, \q
	THETA_D		D1, D1, D3, \q
	THETA_D		D3, D3, \p, \q
.endm

/* a0 ^= RC[r], loaded into the free register t */
.macro IOTA a0, r, t
	ldr		q\t, .LRC + 16*\r
	eor		v\a0\().16b, v\a0\().16b, v\t\().16b
.endm

/* The input words of two nodes, loaded as q8..q15, zipped into v0..v7. */
.macro LOAD_X2 in0, in1
	ldp		q8, q9, [\in0]
	ldp		q10, q11, [\in0, #32]
	ldp		q12, q13, [\in1]
	ldp		q14, q15, [\in1, #32]
	zip1		v0.2d, v8.2d, v12.2d
	zip2		v1.2d, v8.2d, v12.2d
	zip1		v2.2d, v9.2d, v13.2d
	zip2		v3.2d, v9.2d, v13.2d
	zip1		v4.2d, v10.2d, v14.2d
	zip2		v5.2d, v10.2d, v14.2d
	zip1		v6.2d, v11.2d, v15.2d
	zip2		v7.2d, v11.2d, v15.2d
	ldr		q8, .LK1
	ldr		q16, .LK63
.endm

/* void name(unsigned char *output, const unsigned char *input,
 *           uint64_t count)
 * Full pairs in a loop; a single remaining node is hashed alongside a copy
 * of itself, with the copy's digest going to the stack (sp + 64; sp + 96
 * is a 16-byte scratch slot for the kernel). PERMUTATION is round 0 .. 23
 * on v0..v7 (+ the padding lanes), leaving the digests in v25..v28. */
.macro X2_FUNCTION name
	FUNCTION \name
	stp		d8, d9, [sp, #-112]!
	stp		d10, d11, [sp, #16]
	stp		d12, d13, [sp, #32]
	stp		d14, d15, [sp, #48]
	cbz		x2, 2f
1:
	add		x3, x1, #64			/* second node, or the first again */
	add		x4, x0, #32			/* its digest, or the scratch slot */
	add		x5, sp, #64
	cmp		x2, #2
	csel		x3, x3, x1, hs
	csel		x4, x4, x5, hs
	LOAD_X2		x1, x3
	PERMUTATION
	stp		q25, q26, [x0]
	stp		q27, q28, [x4]
	add		x0, x0, #64
	add		x1, x1, #128
	subs		x2, x2, #2
	b.gt		1b
2:
	ldp		d10, d11, [sp, #16]
	ldp		d12, d13, [sp, #32]
	ldp		d14, d15, [sp, #48]
	ldp		d8, d9, [sp], #112
	ret
	END_FUNCTION \name

	KECCAK_RC
.endm
