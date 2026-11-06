/*
 * keccak-f[1600] on one node in the general registers, for interleaving
 * into the AVX2 rounds (keccak256_avx2_x9.S): the integer ALUs of a core
 * sit idle while the vector pipes run the 4-node rounds, and this stream
 * fills them. What counts is the number of macro-ops, as the front end
 * dispatches both streams together.
 *
 * The 25-lane state lives in two 25-qword buffers in the frame (a round
 * reads one and writes the other, like the vector code); with 11
 * registers the round goes row by row:
 *
 *   theta:   D[x] = C[x-1] ^ rotl(C[x+1], 1)       5 rorx + 5 xor
 *            A[i] ^= D[x] in place                 25 xor (read-modify-write)
 *   rho/pi:  B[x] = rotl(A[i], r)                  25 rorx (memory operand)
 *   chi:     A'[i] = B[x] ^ (~B[x+1] & B[x+2])     25 andn, 25 xor, 25 stores
 *   iota:    A'[0] ^= RC                           1 xor (memory operand)
 *   parity:  C'[x] ^= A'[i]                        20 xor, as chi stores
 *
 * 156 macro-ops per round (131 ALU). Theta in place makes rho a single
 * load-and-rotate and frees the D registers before chi, so the parities of
 * the next round accumulate in them: the register set holding C and then
 * D in one round holds B in the next, and the other set the reverse. When
 * two scalar nodes share the registers (SPAR_MEM), each round stores its
 * parities (5 stores) and the next round's theta takes them from memory.
 * rorx (BMI2) and andn (BMI1) write a third register without touching the
 * flags.
 *
 * The round is a list of 65 chunks (SCHUNK): a D, a row's theta, the rho
 * of a lane or the chi of a lane. VHOOK, called by every lane macro of
 * keccak256_avx2.inc, emits chunks at the pace SNUM/SDEN per hook (a
 * credit counter in the assembler), so the scalar instructions spread
 * evenly through the vector round; SFLUSH emits what is left when the
 * vector round ends. Round 0 (sround = 0) takes the parities of the 8
 * data words in the in buffer and writes the padding and zero lanes after
 * theta; round 23 (sround = 23) stops after the 4 digest words of row 0.
 *
 * The including file defines the registers SC0..SC4, SD0..SD4, ST, and
 * RCP (the broadcast round constants, whose first qword serves here).
 * Buffers are addressed as [r9 + offset].
 */

/* d = c1 ^ rotl(c2, 1) from the registers, or (SPAR_MEM, rounds 1..23)
 * from the parities x1 and x2 the previous round stored at s_par */
.macro SD d, c1, c2, x1, x2
#if SPAR_MEM
.if sround
	rorx		\d, qword ptr [r9 + s_par + 8*\x2], 63
	xor		\d, qword ptr [r9 + s_par + 8*\x1]
.else
	rorx		\d, \c2, 63
	xor		\d, \c1
.endif
#else
	rorx		\d, \c2, 63
	xor		\d, \c1
#endif
.endm

/* parity of column x of the data words at in (lanes 0..7, lane 8 = 1,
 * lane 16 = 1 << 63, the rest 0), for round 0 */
.macro SPAR c, x, in
	mov		\c, qword ptr [r9 + \in + 8*\x]
.if \x < 3
	xor		\c, qword ptr [r9 + \in + 8*(\x + 5)]
.endif
.if \x == 1
	xor		\c, qword ptr [rip + .LK63]
.elseif \x == 3
	xor		\c, 1
.endif
.endm

/* theta on lane i at in: A[i] ^= d (round 0: the lanes past the data
 * are written as D, with the padding bits) */
.macro STHETA1 i, d, in
.if sround == 0 && (\i) >= 8
.if (\i) == 8
	mov		ST, \d
	xor		ST, 1
	mov		qword ptr [r9 + \in + 8*(\i)], ST
.elseif (\i) == 16
	mov		ST, \d
	xor		ST, qword ptr [rip + .LK63]
	mov		qword ptr [r9 + \in + 8*(\i)], ST
.else
	mov		qword ptr [r9 + \in + 8*(\i)], \d
.endif
.elseif sround != 23 || (\i) % 6 == 0
	xor		qword ptr [r9 + \in + 8*(\i)], \d
.endif
.endm

/* theta on the five lanes of row y */
.macro STHETA y, d0, d1, d2, d3, d4, in
	STHETA1		5*\y + 0, \d0, \in
	STHETA1		5*\y + 1, \d1, \in
	STHETA1		5*\y + 2, \d2, \in
	STHETA1		5*\y + 3, \d3, \in
	STHETA1		5*\y + 4, \d4, \in
.endm

/* b = rotl(A[i], r) with A[i] at in */
.macro SRHO b, i, r, in
.if \r
	rorx		\b, qword ptr [r9 + \in + 8*\i], 64 - \r
.else
	mov		\b, qword ptr [r9 + \in + 8*\i]
.endif
.endm

/* A'[i] = b0 ^ (~b1 & b2) to lane i at out, iota on lane 0 with the
 * round constant at [RCP + rc], and into the parity c of its column
 * (SPAR_MEM: the complete parities of the last row go to s_par) */
.macro SCHI b0, b1, b2, i, out, rc, c
	andn		ST, \b1, \b2
	xor		ST, \b0
.if \i == 0
	xor		ST, qword ptr [RCP + \rc]
.endif
	mov		qword ptr [r9 + \out + 8*\i], ST
.if sround != 23
.if \i < 5
	mov		\c, ST
.else
	xor		\c, ST
.endif
#if SPAR_MEM
.if \i >= 20
	mov		qword ptr [r9 + s_par + 8*(\i - 20)], \c
.endif
#endif
.endif
.endm

/* chunk n of the round from in to out: the parities are in c0..c4 on
 * entry (round 0: chunks 0..4 compute them), D goes to d0..d4, row B to
 * c0..c4 and the next parities to d0..d4. Row y takes B[x] from lane
 * ((x+3y)%5) + 5x, in the row order of keccak256_avx2.inc. */
.macro SCHUNK n, in, out, rc, c0, c1, c2, c3, c4, d0, d1, d2, d3, d4
.if \n < 5
.if sround == 0
.if \n == 0
	SPAR		\c0, 0, \in
.elseif \n == 1
	SPAR		\c1, 1, \in
.elseif \n == 2
	SPAR		\c2, 2, \in
.elseif \n == 3
	SPAR		\c3, 3, \in
.else
	SPAR		\c4, 4, \in
.endif
.endif
.elseif \n == 5
	SD		\d0, \c4, \c1, 4, 1
.elseif \n == 6
	SD		\d1, \c0, \c2, 0, 2
.elseif \n == 7
	SD		\d2, \c1, \c3, 1, 3
.elseif \n == 8
	SD		\d3, \c2, \c4, 2, 4
.elseif \n == 9
	SD		\d4, \c3, \c0, 3, 0
.elseif \n == 10
	STHETA		0, \d0, \d1, \d2, \d3, \d4, \in
.elseif \n == 11
	STHETA		1, \d0, \d1, \d2, \d3, \d4, \in
.elseif \n == 12
	STHETA		2, \d0, \d1, \d2, \d3, \d4, \in
.elseif \n == 13
	STHETA		3, \d0, \d1, \d2, \d3, \d4, \in
.elseif \n == 14
	STHETA		4, \d0, \d1, \d2, \d3, \d4, \in
.elseif \n == 15
	SRHO		\c0, 0, 0, \in
.elseif \n == 16
	SRHO		\c1, 6, 44, \in
.elseif \n == 17
	SRHO		\c2, 12, 43, \in
.elseif \n == 18
	SRHO		\c3, 18, 21, \in
.elseif \n == 19
	SRHO		\c4, 24, 14, \in
.elseif \n == 20
	SCHI		\c0, \c1, \c2, 0, \out, \rc, \d0
.elseif \n == 21
	SCHI		\c1, \c2, \c3, 1, \out, \rc, \d1
.elseif \n == 22
	SCHI		\c2, \c3, \c4, 2, \out, \rc, \d2
.elseif \n == 23
	SCHI		\c3, \c4, \c0, 3, \out, \rc, \d3
.elseif sround == 23
	/* the digest is complete */
.elseif \n == 24
	SCHI		\c4, \c0, \c1, 4, \out, \rc, \d4
.elseif \n == 25
	SRHO		\c0, 3, 28, \in
.elseif \n == 26
	SRHO		\c1, 9, 20, \in
.elseif \n == 27
	SRHO		\c2, 10, 3, \in
.elseif \n == 28
	SRHO		\c3, 16, 45, \in
.elseif \n == 29
	SRHO		\c4, 22, 61, \in
.elseif \n == 30
	SCHI		\c0, \c1, \c2, 5, \out, \rc, \d0
.elseif \n == 31
	SCHI		\c1, \c2, \c3, 6, \out, \rc, \d1
.elseif \n == 32
	SCHI		\c2, \c3, \c4, 7, \out, \rc, \d2
.elseif \n == 33
	SCHI		\c3, \c4, \c0, 8, \out, \rc, \d3
.elseif \n == 34
	SCHI		\c4, \c0, \c1, 9, \out, \rc, \d4
.elseif \n == 35
	SRHO		\c0, 1, 1, \in
.elseif \n == 36
	SRHO		\c1, 7, 6, \in
.elseif \n == 37
	SRHO		\c2, 13, 25, \in
.elseif \n == 38
	SRHO		\c3, 19, 8, \in
.elseif \n == 39
	SRHO		\c4, 20, 18, \in
.elseif \n == 40
	SCHI		\c0, \c1, \c2, 10, \out, \rc, \d0
.elseif \n == 41
	SCHI		\c1, \c2, \c3, 11, \out, \rc, \d1
.elseif \n == 42
	SCHI		\c2, \c3, \c4, 12, \out, \rc, \d2
.elseif \n == 43
	SCHI		\c3, \c4, \c0, 13, \out, \rc, \d3
.elseif \n == 44
	SCHI		\c4, \c0, \c1, 14, \out, \rc, \d4
.elseif \n == 45
	SRHO		\c0, 4, 27, \in
.elseif \n == 46
	SRHO		\c1, 5, 36, \in
.elseif \n == 47
	SRHO		\c2, 11, 10, \in
.elseif \n == 48
	SRHO		\c3, 17, 15, \in
.elseif \n == 49
	SRHO		\c4, 23, 56, \in
.elseif \n == 50
	SCHI		\c0, \c1, \c2, 15, \out, \rc, \d0
.elseif \n == 51
	SCHI		\c1, \c2, \c3, 16, \out, \rc, \d1
.elseif \n == 52
	SCHI		\c2, \c3, \c4, 17, \out, \rc, \d2
.elseif \n == 53
	SCHI		\c3, \c4, \c0, 18, \out, \rc, \d3
.elseif \n == 54
	SCHI		\c4, \c0, \c1, 19, \out, \rc, \d4
.elseif \n == 55
	SRHO		\c0, 2, 62, \in
.elseif \n == 56
	SRHO		\c1, 8, 55, \in
.elseif \n == 57
	SRHO		\c2, 14, 39, \in
.elseif \n == 58
	SRHO		\c3, 15, 41, \in
.elseif \n == 59
	SRHO		\c4, 21, 2, \in
.elseif \n == 60
	SCHI		\c0, \c1, \c2, 20, \out, \rc, \d0
.elseif \n == 61
	SCHI		\c1, \c2, \c3, 21, \out, \rc, \d1
.elseif \n == 62
	SCHI		\c2, \c3, \c4, 22, \out, \rc, \d2
.elseif \n == 63
	SCHI		\c3, \c4, \c0, 23, \out, \rc, \d3
.elseif \n == 64
	SCHI		\c4, \c0, \c1, 24, \out, \rc, \d4
.endif
.endm
#define SCHUNKS		65

/* the chunk sn of the current round with the register sets in the order
 * of this round (sswap) */
.macro SCHUNK_CUR
.if sswap
	SCHUNK		sn, s_in, s_out, s_rc, SD0, SD1, SD2, SD3, SD4, SC0, SC1, SC2, SC3, SC4
.else
	SCHUNK		sn, s_in, s_out, s_rc, SC0, SC1, SC2, SC3, SC4, SD0, SD1, SD2, SD3, SD4
.endif
.endm

/* start the scalar round r (0, 1 or 23) from in to out with the round
 * constant at [RCP + rc] and the parities in SC0..SC4 (swap = 0) or
 * SD0..SD4 (swap = 1), or at par with SPAR_MEM: the hooks emit its chunks
 * from here on */
.macro SROUND_BEGIN r, in, out, rc, swap, par=0
	.set		sround, \r
	.set		s_in, \in
	.set		s_out, \out
	.set		s_rc, \rc
	.set		sswap, \swap
	.set		s_par, \par
	.set		sn, 0
	.set		scredit, 0
.endm

/* the next chunk of the current scalar round, if any */
.macro SNEXT
.if sn < SCHUNKS
	SCHUNK_CUR
	.set		sn, sn + 1
.endif
.endm

/* the rest of the current scalar round */
.macro SFLUSH
.rept SCHUNKS - sn
	SNEXT
.endr
.endm

/* the vector lane hook: SNUM/SDEN chunks per call (at most two); with
 * SNUM_T / SNUM_R / SNUM_C defined, that many per theta, rho and chi hook */
#define VHOOK_DEFINED
.macro VHOOK kind
#ifdef SNUM_T
.ifc \kind, t
	.set		scredit, scredit + SNUM_T
.endif
.ifc \kind, r
	.set		scredit, scredit + SNUM_R
.endif
.ifc \kind, c
	.set		scredit, scredit + SNUM_C
.endif
#else
	.set		scredit, scredit + SNUM
#endif
.if scredit >= SDEN
	.set		scredit, scredit - SDEN
	SNEXT
.endif
.if scredit >= SDEN
	.set		scredit, scredit - SDEN
	SNEXT
.endif
.endm
