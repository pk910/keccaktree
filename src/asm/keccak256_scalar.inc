/*
 * Keccak-f[1600] on one node in the general registers with lazy rotations,
 * shared by keccak256_scalar_x1.S and keccak256_sha3_x3.S.
 *
 * EOR and BIC rotate their second operand for free, so rho is never done:
 * the register of lane i holds its value rotated right by O<i>, an offset
 * the assembler tracks in the symbols O0..O24 (SNEXT updates them after
 * each round), and every EOR/BIC rotates its second operand by the
 * difference of the two offsets. Only the four digest words are rotated
 * back at the end. The round constants need no rotation because lane 0's
 * offset is always 0 (its rho rotation is 0).
 *
 * Registers: the 25 lanes plus five for the column parities C0..C4, which
 * turn into D0..D3 (D4 is not formed: the five lanes of column 4 take
 * C3 ^ rotl(C0, 1) in two EORs each, which keeps the state in 30 registers
 * and leaves x18 alone for macOS). As in keccak256_neon.inc the ROUND lines
 * name every lane's register and the pi moves are register renaming; chi
 * writes two lanes into free registers and the rest over their inputs.
 * 106 instructions per round.
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

/* d = a ^ b, d = a & ~b, with b brought from offset ob to a's offset oa */
.macro SXOR d, a, b, oa, ob
	eor		x\d, x\a, x\b, ror #(((\oa) - (\ob)) & 63)
.endm
.macro SBIC d, a, b, oa, ob
	bic		x\d, x\a, x\b, ror #(((\oa) - (\ob)) & 63)
.endm

#define SARGS s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, c0, c1, c2, c3, c4
#define SPASS \s0, \s1, \s2, \s3, \s4, \s5, \s6, \s7, \s8, \s9, \s10, \s11, \s12, \s13, \s14, \s15, \s16, \s17, \s18, \s19, \s20, \s21, \s22, \s23, \s24, \c0, \c1, \c2, \c3, \c4

/* parities C0..C4 (at the offsets of row 0), column 4 of the state
 * updated with D4 = C3 ^ rotl(C0, 1), then D1, D3, D0, D2 over
 * c0, c2, c4, c1 in that order (each C's last use first); c3 is free */
.macro STHETA SARGS
	SXOR		\c0, \s0, \s5, O0, O5
	SXOR		\c1, \s1, \s6, O1, O6
	SXOR		\c2, \s2, \s7, O2, O7
	SXOR		\c3, \s3, \s8, O3, O8
	SXOR		\c4, \s4, \s9, O4, O9
	SXOR		\c0, \c0, \s10, O0, O10
	SXOR		\c1, \c1, \s11, O1, O11
	SXOR		\c2, \c2, \s12, O2, O12
	SXOR		\c3, \c3, \s13, O3, O13
	SXOR		\c4, \c4, \s14, O4, O14
	SXOR		\c0, \c0, \s15, O0, O15
	SXOR		\c1, \c1, \s16, O1, O16
	SXOR		\c2, \c2, \s17, O2, O17
	SXOR		\c3, \c3, \s18, O3, O18
	SXOR		\c4, \c4, \s19, O4, O19
	SXOR		\c0, \c0, \s20, O0, O20
	SXOR		\c1, \c1, \s21, O1, O21
	SXOR		\c2, \c2, \s22, O2, O22
	SXOR		\c3, \c3, \s23, O3, O23
	SXOR		\c4, \c4, \s24, O4, O24
	SXOR		\s4, \s4, \c3, O4, O3
	SXOR		\s9, \s9, \c3, O9, O3
	SXOR		\s14, \s14, \c3, O14, O3
	SXOR		\s19, \s19, \c3, O19, O3
	SXOR		\s24, \s24, \c3, O24, O3
	SXOR		\s4, \s4, \c0, O4, O0 + 1
	SXOR		\s9, \s9, \c0, O9, O0 + 1
	SXOR		\s14, \s14, \c0, O14, O0 + 1
	SXOR		\s19, \s19, \c0, O19, O0 + 1
	SXOR		\s24, \s24, \c0, O24, O0 + 1
	SXOR		\c0, \c0, \c2, O0, O2 + 1
	SXOR		\c2, \c2, \c4, O2, O4 + 1
	SXOR		\c4, \c4, \c1, O4, O1 + 1
	SXOR		\c1, \c1, \c3, O1, O3 + 1
.endm

/* theta on columns 0..3: D0 in c4, D1 in c0, D2 in c1, D3 in c2 */
.macro SRHO SARGS
	SXOR		\s0, \s0, \c4, O0, O4
	SXOR		\s1, \s1, \c0, O1, O0
	SXOR		\s2, \s2, \c1, O2, O1
	SXOR		\s3, \s3, \c2, O3, O2
	SXOR		\s5, \s5, \c4, O5, O4
	SXOR		\s6, \s6, \c0, O6, O0
	SXOR		\s7, \s7, \c1, O7, O1
	SXOR		\s8, \s8, \c2, O8, O2
	SXOR		\s10, \s10, \c4, O10, O4
	SXOR		\s11, \s11, \c0, O11, O0
	SXOR		\s12, \s12, \c1, O12, O1
	SXOR		\s13, \s13, \c2, O13, O2
	SXOR		\s15, \s15, \c4, O15, O4
	SXOR		\s16, \s16, \c0, O16, O0
	SXOR		\s17, \s17, \c1, O17, O1
	SXOR		\s18, \s18, \c2, O18, O2
	SXOR		\s20, \s20, \c4, O20, O4
	SXOR		\s21, \s21, \c0, O21, O0
	SXOR		\s22, \s22, \c1, O22, O1
	SXOR		\s23, \s23, \c2, O23, O2
.endm

/* chi on a row, b[x] at offset o[x]: out[x] = b[x] ^ (~b[x+1] & b[x+2])
 * with out0..4 -> f0, f1, b2, b0, b1 (b3, b4 freed). Outputs 3 and 4 are
 * built in place: each input's last use is the BIC that starts the output
 * taking its place. */
.macro SCHI b0, b1, b2, b3, b4, f0, f1, o0, o1, o2, o3, o4
	SBIC		\f1, \b2, \b1, \o2, \o1
	SXOR		\f0, \b0, \f1, \o0, \o2
	SBIC		\f1, \b3, \b2, \o3, \o2
	SXOR		\f1, \b1, \f1, \o1, \o3
	SBIC		\b1, \b1, \b0, \o1, \o0
	SBIC		\b0, \b0, \b4, \o0, \o4
	SXOR		\b0, \b3, \b0, \o3, \o0
	SXOR		\b1, \b4, \b1, \o4, \o1
	SBIC		\b3, \b4, \b3, \o4, \o3
	SXOR		\b2, \b2, \b3, \o2, \o4
.endm

/* row y of chi takes B[x] from lane ((x+3y)%5) + 5x at offset O + R */
.macro SCHI_ROW0 r, SARGS
	ldr		x\c0, .LRC + 16*\r
	SCHI		\s0, \s6, \s12, \s18, \s24, \c3, \c4, O0 + R0, O6 + R6, O12 + R12, O18 + R18, O24 + R24
	eor		x\c3, x\c3, x\c0
.endm
.macro SCHI_ROW1 SARGS
	SCHI		\s3, \s9, \s10, \s16, \s22, \s18, \s24, O3 + R3, O9 + R9, O10 + R10, O16 + R16, O22 + R22
.endm
.macro SCHI_ROW2 SARGS
	SCHI		\s1, \s7, \s13, \s19, \s20, \s16, \s22, O1 + R1, O7 + R7, O13 + R13, O19 + R19, O20 + R20
.endm
.macro SCHI_ROW3 SARGS
	SCHI		\s4, \s5, \s11, \s17, \s23, \s19, \s20, O4 + R4, O5 + R5, O11 + R11, O17 + R17, O23 + R23
.endm
.macro SCHI_ROW4 SARGS
	SCHI		\s2, \s8, \s14, \s15, \s21, \s17, \s23, O2 + R2, O8 + R8, O14 + R14, O15 + R15, O21 + R21
.endm

/* the lane offsets after a round: lane x + 5y came from lane
 * ((x+3y)%5) + 5x and gained its rho rotation */
.macro SNEXT
	.set N0, (O0 + R0) & 63
	.set N1, (O6 + R6) & 63
	.set N2, (O12 + R12) & 63
	.set N3, (O18 + R18) & 63
	.set N4, (O24 + R24) & 63
	.set N5, (O3 + R3) & 63
	.set N6, (O9 + R9) & 63
	.set N7, (O10 + R10) & 63
	.set N8, (O16 + R16) & 63
	.set N9, (O22 + R22) & 63
	.set N10, (O1 + R1) & 63
	.set N11, (O7 + R7) & 63
	.set N12, (O13 + R13) & 63
	.set N13, (O19 + R19) & 63
	.set N14, (O20 + R20) & 63
	.set N15, (O4 + R4) & 63
	.set N16, (O5 + R5) & 63
	.set N17, (O11 + R11) & 63
	.set N18, (O17 + R17) & 63
	.set N19, (O23 + R23) & 63
	.set N20, (O2 + R2) & 63
	.set N21, (O8 + R8) & 63
	.set N22, (O14 + R14) & 63
	.set N23, (O15 + R15) & 63
	.set N24, (O21 + R21) & 63
	.irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24
	.set O\i, N\i
	.endr
.endm

.macro SROUND r, SARGS
	STHETA		SPASS
	SRHO		SPASS
	SCHI_ROW0	\r, SPASS
	SCHI_ROW1	SPASS
	SCHI_ROW2	SPASS
	SCHI_ROW3	SPASS
	SCHI_ROW4	SPASS
	SNEXT
.endm

/* round 0 on lane i in x(i) (x19.. for lanes 18..24): input words in
 * x0..x7, 0x01 in x8, 0x80..0 in x16, the rest zero (not initialised: a
 * zero lane after theta is just D, so they get a copy). Every offset is 0. */
.macro SFIRST_ROUND
	.irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24
	.set O\i, 0
	.endr
	eor		x26, x0, x5
	eor		x27, x1, x6
	eor		x27, x27, x16
	eor		x28, x2, x7
	eor		x29, x3, x8
	mov		x30, x4
	eor		x4, x4, x29
	eor		x4, x4, x26, ror #63
	eor		x9, x29, x26, ror #63
	mov		x14, x9
	mov		x20, x9
	mov		x25, x9
	eor		x26, x26, x28, ror #63		/* D1 */
	eor		x28, x28, x30, ror #63		/* D3 */
	eor		x30, x30, x27, ror #63		/* D0 */
	eor		x27, x27, x29, ror #63		/* D2 */
	eor		x0, x0, x30
	eor		x1, x1, x26
	eor		x2, x2, x27
	eor		x3, x3, x28
	eor		x5, x5, x30
	eor		x6, x6, x26
	eor		x7, x7, x27
	eor		x8, x8, x28
	mov		x10, x30
	mov		x11, x26
	mov		x12, x27
	mov		x13, x28
	mov		x15, x30
	eor		x16, x16, x26
	mov		x17, x27
	mov		x19, x28
	mov		x21, x30
	mov		x22, x26
	mov		x23, x27
	mov		x24, x28
	SCHI_ROW0	0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW1	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW2	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW3	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SCHI_ROW4	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30
	SNEXT
.endm

/* round 23: row 0, x = 0..3 only, rotated back and stored at
 * [[sp + OUT_SLOT] + OUT_OFF] */
.macro SLAST_ROUND SARGS
	STHETA		SPASS
	SXOR		\s0, \s0, \c4, O0, O4
	SXOR		\s6, \s6, \c0, O6, O0
	SXOR		\s12, \s12, \c1, O12, O1
	SXOR		\s18, \s18, \c2, O18, O2
	.set L0, O0 + R0
	.set L1, O6 + R6
	.set L2, O12 + R12
	.set L3, O18 + R18
	.set L4, O24 + R24
	ldr		x\c0, .LRC + 16*23
	SBIC		\c4, \s12, \s6, L2, L1
	SXOR		\c3, \s0, \c4, L0, L2
	SBIC		\c4, \s18, \s12, L3, L2
	SXOR		\c4, \s6, \c4, L1, L3
	SBIC		\s0, \s0, \s24, L0, L4
	SXOR		\s0, \s18, \s0, L3, L0
	SBIC		\s18, \s24, \s18, L4, L3
	SXOR		\s12, \s12, \s18, L2, L4
	eor		x\c3, x\c3, x\c0
	ldr		x\c0, [sp, #OUT_SLOT]
	ror		x\c4, x\c4, #((64 - L1) & 63)
	ror		x\s12, x\s12, #((64 - L2) & 63)
	ror		x\s0, x\s0, #((64 - L3) & 63)
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
