/*
 * void keccaktree_keccak256_neon_x3(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 3 at a time on
 * ARMv8.0 cores without FEAT_SHA3 (Neoverse N1, Graviton 2, Cortex-A7x):
 * two nodes in the vector registers (keccak256_neon.inc,
 * keccak256_asimd.inc, as keccak256_neon_x2.S) and one in the general
 * registers with lazy rotations (keccak256_scalar.inc, as
 * keccak256_scalar_x1.S), their rounds interleaved. Fewer than 3 remaining
 * nodes go to keccak256_scalar_x1, which takes as long for them.
 *
 * On Neoverse N1 neon_x2 is bound by its two vector pipes (156 vector
 * instructions per round, ~84 cycles) and scalar_x1 by the three integer
 * ALUs (106 instructions, ~35 cycles); both streams in one instruction
 * window share the 4-wide front end (262 instructions per round, ~66
 * cycles) and the vector pipes stay the bound, so the scalar node is
 * nearly free: 227 ns per node against 276 for scalar_x1 and 340 for
 * neon_x2 (count 256). The pieces alternate every 5..15 instructions so
 * the out-of-order window (128 entries, less than one round) always holds
 * work for every pipe.
 *
 * Each ROUND3 line names the 25 lane registers and the free pair of the
 * vector stream, then the 25 lane registers and the five parity registers
 * of the scalar stream.
 */
#ifdef __aarch64__
#include "keccak256_arm_frame.inc"
#define OUT_SLOT	160
#define OUT_OFF		64
#include "keccak256_scalar.inc"

#include "keccak256_neon.inc"
#include "keccak256_asimd.inc"

/* one round of both streams: the vector theta, then the rho and chi of
 * each row, with the scalar pieces in between */
.macro ROUND3 r, ARGS, SARGS
	THETA_C01	PASS
	STHETA_C01	SPASS
	THETA_C234	PASS
	STHETA_C2	SPASS
	THETA_DD	PASS
	STHETA_C3	SPASS
	STHETA_C4	SPASS
	RHO_ROW		\a0, \a6, \a12, \a18, \a24, D0, D1, D2, D3, D4, 0, 44, 43, 21, 14, \p, \q
	STHETA_COL4	SPASS
	CHI_ROW		\p, \q, \a0, \a6, \a12, \a18, \a24
	STHETA_D	SPASS
	RHO_ROW		\a3, \a9, \a10, \a16, \a22, D3, D4, D0, D1, D2, 28, 20, 3, 45, 61, \a6, \a12
	SRHO_ROWS01	SPASS
	CHI_ROW		\a6, \a12, \a3, \a9, \a10, \a16, \a22
	RHO_ROW		\a1, \a7, \a13, \a19, \a20, D1, D2, D3, D4, D0, 1, 6, 25, 8, 18, \a9, \a10
	SRHO_ROWS234	SPASS
	CHI_ROW		\a9, \a10, \a1, \a7, \a13, \a19, \a20
	SCHI_ROW0	\r, SPASS
	RHO_ROW		\a4, \a5, \a11, \a17, \a23, D4, D0, D1, D2, D3, 27, 36, 10, 15, 56, \a7, \a13
	SCHI_ROW1	SPASS
	CHI_ROW		\a7, \a13, \a4, \a5, \a11, \a17, \a23
	SCHI_ROW2	SPASS
	ROUND_ROW4	\r, PASS
	SCHI_ROW3	SPASS
	SRHO_LANE2	SPASS
	SCHI_ROW4	SPASS
	SNEXT
.endm

.macro LAST_ROUND3 ARGS, SARGS
	THETA_C01	PASS
	THETA_C234	PASS
	SLAST_ROUND	SPASS
	THETA_DD	PASS
	LAST_ROW	PASS
.endm

	FUNCTION keccaktree_keccak256_neon_x3
	cmp		x2, #3
	b.lo		3f
	stp		x29, x30, [sp, #-192]!
	stp		x19, x20, [sp, #16]
	stp		x21, x22, [sp, #32]
	stp		x23, x24, [sp, #48]
	stp		x25, x26, [sp, #64]
	stp		x27, x28, [sp, #80]
	stp		d8, d9, [sp, #96]
	stp		d10, d11, [sp, #112]
	stp		d12, d13, [sp, #128]
	stp		d14, d15, [sp, #144]
1:
	stp		x0, x1, [sp, #160]
	str		x2, [sp, #176]
	add		x3, x1, #64
	LOAD_X2		x1, x3
	add		x1, x1, #128
	SLOAD		x1
	FIRST_ROUND_A
	SFIRST_ROUND_THETA
	FIRST_ROUND_B
	SFIRST_ROUND_CHI
	ROUND3		1, 18, 24, 0, 30, 31, 16, 22, 3, 6, 12, 19, 20, 1, 9, 10, 17, 23, 4, 7, 13, 15, 21, 2, 5, 11, 8, 14, 29, 30, 12, 0, 6, 19, 25, 10, 3, 9, 16, 23, 13, 1, 7, 20, 21, 11, 4, 5, 17, 24, 14, 2, 8, 26, 27, 28, 15, 22
	ROUND3		2, 7, 11, 18, 8, 14, 23, 2, 30, 22, 1, 13, 15, 24, 12, 19, 4, 5, 31, 3, 9, 17, 21, 0, 16, 20, 6, 10, 15, 22, 13, 29, 25, 4, 8, 16, 0, 9, 21, 14, 1, 30, 10, 5, 17, 23, 6, 19, 11, 2, 7, 12, 3, 26, 27, 28, 20, 24
	ROUND3		3, 3, 20, 7, 6, 10, 5, 0, 8, 2, 24, 9, 17, 11, 1, 13, 31, 16, 14, 30, 12, 4, 21, 18, 23, 15, 22, 19, 20, 24, 1, 15, 8, 6, 3, 21, 29, 9, 17, 7, 30, 22, 16, 19, 11, 14, 25, 4, 23, 12, 10, 13, 0, 26, 27, 28, 5, 2
	ROUND3		4, 30, 15, 3, 22, 19, 16, 18, 6, 0, 11, 12, 4, 20, 24, 9, 14, 23, 10, 8, 1, 31, 21, 7, 5, 17, 2, 13, 5, 2, 30, 20, 3, 25, 0, 17, 15, 9, 11, 10, 22, 24, 21, 4, 23, 7, 8, 6, 14, 13, 16, 1, 29, 26, 27, 28, 19, 12
	ROUND3		5, 8, 17, 30, 2, 13, 23, 7, 22, 18, 20, 1, 31, 15, 11, 12, 10, 5, 19, 6, 24, 14, 21, 3, 16, 4, 0, 9, 19, 12, 22, 5, 0, 8, 29, 11, 20, 9, 23, 16, 24, 2, 17, 6, 14, 10, 3, 25, 7, 1, 21, 30, 15, 26, 27, 28, 4, 13
	ROUND3		6, 6, 4, 8, 0, 9, 5, 3, 2, 7, 15, 24, 14, 17, 20, 1, 19, 16, 13, 22, 11, 10, 21, 30, 23, 31, 18, 12, 4, 13, 24, 19, 29, 3, 15, 23, 5, 9, 14, 21, 2, 12, 11, 25, 7, 16, 0, 8, 10, 30, 17, 22, 20, 26, 27, 28, 6, 1
	ROUND3		7, 22, 31, 6, 18, 12, 16, 30, 0, 3, 17, 11, 10, 4, 15, 24, 13, 23, 9, 2, 20, 19, 21, 8, 5, 14, 7, 1, 6, 1, 2, 4, 15, 0, 20, 14, 19, 9, 7, 17, 12, 13, 23, 8, 10, 21, 29, 3, 16, 22, 11, 24, 5, 26, 27, 28, 25, 30
	ROUND3		8, 2, 14, 22, 7, 1, 23, 8, 18, 30, 4, 20, 19, 31, 17, 11, 9, 5, 12, 0, 15, 13, 21, 6, 16, 10, 3, 24, 25, 30, 12, 6, 20, 29, 5, 7, 4, 9, 10, 11, 13, 1, 14, 3, 16, 17, 15, 0, 21, 24, 23, 2, 19, 26, 27, 28, 8, 22
	ROUND3		9, 0, 10, 2, 3, 24, 5, 6, 7, 8, 31, 15, 13, 14, 4, 20, 12, 16, 1, 18, 17, 9, 21, 22, 23, 19, 30, 11, 8, 22, 13, 25, 5, 15, 19, 10, 6, 9, 16, 23, 1, 30, 7, 0, 21, 11, 20, 29, 17, 2, 14, 12, 4, 26, 27, 28, 3, 24
	ROUND3		10, 18, 19, 0, 30, 11, 16, 22, 3, 6, 14, 17, 9, 10, 31, 15, 1, 23, 24, 7, 4, 12, 21, 2, 5, 13, 8, 20, 3, 24, 1, 8, 19, 20, 4, 16, 25, 9, 21, 14, 30, 22, 10, 29, 17, 23, 5, 15, 11, 12, 7, 13, 6, 26, 27, 28, 0, 2
	ROUND3		11, 7, 13, 18, 8, 20, 23, 2, 30, 22, 10, 4, 12, 19, 14, 17, 24, 5, 11, 3, 31, 1, 21, 0, 16, 9, 6, 15, 0, 2, 30, 3, 4, 5, 6, 21, 8, 9, 17, 7, 22, 24, 16, 15, 11, 14, 19, 20, 23, 13, 10, 1, 25, 26, 27, 28, 29, 12
	ROUND3		12, 3, 9, 7, 6, 15, 5, 0, 8, 2, 19, 31, 1, 13, 10, 4, 11, 16, 20, 30, 14, 24, 21, 18, 23, 12, 22, 17, 29, 12, 22, 0, 6, 19, 25, 17, 3, 9, 11, 10, 24, 2, 21, 20, 23, 7, 4, 5, 14, 1, 16, 30, 8, 26, 27, 28, 15, 13
	ROUND3		13, 30, 12, 3, 22, 17, 16, 18, 6, 0, 13, 14, 24, 9, 19, 31, 20, 23, 15, 8, 10, 11, 21, 7, 5, 1, 2, 4, 15, 13, 24, 29, 25, 4, 8, 11, 0, 9, 23, 16, 2, 12, 17, 5, 14, 10, 6, 19, 7, 30, 21, 22, 3, 26, 27, 28, 20, 1
	ROUND3		14, 8, 1, 30, 2, 4, 23, 7, 22, 18, 9, 10, 11, 12, 13, 14, 15, 5, 17, 6, 19, 20, 21, 3, 16, 24, 0, 31, 20, 1, 2, 15, 8, 6, 3, 23, 29, 9, 14, 21, 12, 13, 11, 19, 7, 16, 25, 4, 10, 22, 17, 24, 0, 26, 27, 28, 5, 30
	ROUND3		15, 6, 24, 8, 0, 31, 5, 3, 2, 7, 12, 19, 20, 1, 9, 10, 17, 16, 4, 22, 13, 15, 21, 30, 23, 11, 18, 14, 5, 30, 12, 20, 3, 25, 0, 14, 15, 9, 7, 17, 13, 1, 23, 4, 10, 21, 8, 6, 16, 24, 11, 2, 29, 26, 27, 28, 19, 22
	ROUND3		16, 22, 11, 6, 18, 14, 16, 30, 0, 3, 1, 13, 15, 24, 12, 19, 4, 23, 31, 2, 9, 17, 21, 8, 5, 20, 7, 10, 19, 22, 13, 5, 0, 8, 29, 7, 20, 9, 10, 11, 1, 30, 14, 6, 16, 17, 3, 25, 21, 2, 23, 12, 15, 26, 27, 28, 4, 24
	ROUND3		17, 2, 20, 22, 7, 10, 23, 8, 18, 30, 24, 9, 17, 11, 1, 13, 31, 5, 14, 0, 12, 4, 21, 6, 16, 15, 3, 19, 4, 24, 1, 19, 29, 3, 15, 10, 5, 9, 16, 23, 30, 22, 7, 25, 21, 11, 0, 8, 17, 12, 14, 13, 20, 26, 27, 28, 6, 2
	ROUND3		18, 0, 15, 2, 3, 19, 5, 6, 7, 8, 11, 12, 4, 20, 24, 9, 14, 16, 10, 18, 1, 31, 21, 22, 23, 17, 30, 13, 6, 2, 30, 4, 15, 0, 20, 16, 19, 9, 21, 14, 22, 24, 10, 8, 17, 23, 29, 3, 11, 13, 7, 1, 5, 26, 27, 28, 25, 12
	ROUND3		19, 18, 17, 0, 30, 13, 16, 22, 3, 6, 20, 1, 31, 15, 11, 12, 10, 23, 19, 7, 24, 14, 21, 2, 5, 4, 8, 9, 25, 12, 22, 6, 20, 29, 5, 21, 4, 9, 17, 7, 24, 2, 16, 3, 11, 14, 15, 0, 23, 1, 10, 30, 19, 26, 27, 28, 8, 13
	ROUND3		20, 7, 4, 18, 8, 9, 23, 2, 30, 22, 15, 24, 14, 17, 20, 1, 19, 5, 13, 3, 11, 10, 21, 0, 16, 31, 6, 12, 8, 13, 24, 25, 5, 15, 19, 17, 6, 9, 11, 10, 2, 12, 21, 0, 23, 7, 20, 29, 14, 30, 16, 22, 4, 26, 27, 28, 3, 1
	ROUND3		21, 3, 31, 7, 6, 12, 5, 0, 8, 2, 17, 11, 10, 4, 15, 24, 13, 16, 9, 30, 20, 19, 21, 18, 23, 14, 22, 1, 3, 1, 2, 8, 19, 20, 4, 11, 25, 9, 23, 16, 12, 13, 17, 29, 14, 10, 5, 15, 7, 22, 21, 24, 6, 26, 27, 28, 0, 30
	ROUND3		22, 30, 14, 3, 22, 1, 16, 18, 6, 0, 4, 20, 19, 31, 17, 11, 9, 23, 12, 8, 15, 13, 21, 7, 5, 10, 2, 24, 0, 30, 12, 3, 4, 5, 6, 23, 8, 9, 14, 21, 13, 1, 11, 15, 7, 16, 19, 20, 10, 24, 17, 2, 25, 26, 27, 28, 29, 22
	LAST_ROUND3	8, 10, 30, 2, 24, 23, 7, 22, 18, 31, 15, 13, 14, 4, 20, 12, 5, 1, 6, 17, 9, 21, 3, 16, 19, 0, 11, 29, 22, 13, 0, 6, 19, 25, 14, 3, 9, 7, 17, 1, 30, 23, 20, 10, 21, 4, 5, 16, 2, 11, 12, 8, 26, 27, 28, 15, 24
	ldp		x0, x1, [sp, #160]
	ldr		x2, [sp, #176]
	stp		q25, q26, [x0]
	stp		q27, q28, [x0, #32]
	add		x0, x0, #96
	add		x1, x1, #192
	sub		x2, x2, #3
	cmp		x2, #3
	b.hs		1b
	ldp		x19, x20, [sp, #16]
	ldp		x21, x22, [sp, #32]
	ldp		x23, x24, [sp, #48]
	ldp		x25, x26, [sp, #64]
	ldp		x27, x28, [sp, #80]
	ldp		d8, d9, [sp, #96]
	ldp		d10, d11, [sp, #112]
	ldp		d12, d13, [sp, #128]
	ldp		d14, d15, [sp, #144]
	ldp		x29, x30, [sp], #192
	cbz		x2, 2f
3:
#ifdef __APPLE__
	b		_keccaktree_keccak256_scalar_x1
#else
	b		keccaktree_keccak256_scalar_x1
#endif
2:
	ret
	END_FUNCTION keccaktree_keccak256_neon_x3

	KECCAK_RC
	ASIMD_TABLES
	GNU_STACK_NOTE
#endif
