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
 * On Neoverse N1 neon_x2 is bound by its two vector pipes (157 vector
 * instructions per round, ~80 cycles) and scalar_x1 by the three integer
 * ALUs (102 instructions, ~34 cycles); both streams in one instruction
 * window share the 4-wide front end (265 instructions per round, ~66
 * cycles) and the vector pipes stay the bound, so the scalar node is
 * nearly free: 216 ns per node against 271 for scalar_x1 and 324 for
 * neon_x2 (count 256; hashtree's sha256 neon_x4 takes 257). The pieces
 * alternate every 10..25 instructions so the out-of-order window (128
 * entries, less than one round) always holds work for every pipe.
 *
 * Each ROUND3 line names the 25 lane registers, the five D registers and
 * the free pair of the vector stream (keccak256_asimd.inc), then the 25
 * lane registers and the five parity registers of the scalar stream. The
 * frame: callee-saved registers, output/input/count (160..176), the scalar
 * stream's spill slot (184) and the vector stream's (192).
 */
#ifdef __aarch64__
#include "keccak256_arm_frame.inc"
#define OUT_SLOT	160
#define OUT_OFF		64
#define VSPILL		192
#include "keccak256_scalar.inc"

#include "keccak256_neon.inc"
#include "keccak256_asimd.inc"

/* one round of both streams: the vector pieces of keccak256_asimd.inc
 * with the scalar theta, rho and chi rows in the gaps */
.macro ROUND3 r, VARGS, SARGS
	V_THETA		VPASS
	STHETA_C01	SPASS
	STHETA_C2	SPASS
	V_RHO0		VPASS
	STHETA_C3	SPASS
	STHETA_C4	SPASS
	V_PAIR01	VPASS
	STHETA_COL4	SPASS
	STHETA_D	SPASS
	V_PAIR12	VPASS
	SRHO_ROWS01	SPASS
	SRHO_ROWS234	SPASS
	V_PAIR23	VPASS
	SCHI_ROW0	\r, SPASS
	SCHI_ROW1	SPASS
	V_PAIR34	VPASS
	SCHI_ROW2	SPASS
	SCHI_ROW3	SPASS
	V_CHI4		\r, VPASS
	SRHO_LANE2	SPASS
	SCHI_ROW4	SPASS
	SNEXT
.endm

.macro LAST_ROUND3 o0, o1, o2, o3, VARGS, SARGS
	V_THETA_LAST	VPASS
	SLAST_ROUND	SPASS
	V_LAST_ROW	\o0, \o1, \o2, \o3, VPASS
.endm

	FUNCTION keccaktree_keccak256_neon_x3
	cmp		x2, #3
	b.lo		3f
	stp		x29, x30, [sp, #-208]!
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
	ROUND3		1, 18, 24, 0, 30, 31, 16, 22, 3, 6, 12, 19, 20, 1, 9, 10, 17, 23, 4, 7, 13, 15, 21, 2, 5, 11, 25, 26, 27, 28, 29, 8, 14, 29, 30, 12, 0, 6, 19, 25, 10, 3, 9, 16, 23, 13, 1, 7, 20, 21, 11, 4, 5, 17, 24, 14, 2, 8, 26, 27, 28, 15, 22
	ROUND3		2, 14, 0, 22, 8, 18, 1, 7, 12, 11, 30, 19, 23, 3, 2, 24, 9, 13, 16, 15, 31, 20, 4, 29, 27, 28, 5, 6, 10, 17, 21, 25, 26, 15, 22, 13, 29, 25, 4, 8, 16, 0, 9, 21, 14, 1, 30, 10, 5, 17, 23, 6, 19, 11, 2, 7, 12, 3, 26, 27, 28, 20, 24
	ROUND3		3, 26, 22, 7, 25, 14, 3, 15, 30, 28, 8, 19, 13, 12, 29, 0, 2, 31, 1, 20, 18, 23, 16, 21, 10, 17, 4, 5, 6, 9, 11, 24, 27, 20, 24, 1, 15, 8, 6, 3, 21, 29, 9, 17, 7, 30, 22, 16, 19, 11, 14, 25, 4, 23, 12, 10, 13, 0, 26, 27, 28, 5, 2
	ROUND3		4, 27, 7, 15, 24, 26, 12, 20, 8, 17, 25, 19, 31, 30, 21, 22, 29, 18, 3, 23, 14, 13, 1, 11, 6, 9, 0, 2, 4, 5, 10, 16, 28, 5, 2, 30, 20, 3, 25, 0, 17, 15, 9, 11, 10, 22, 24, 21, 4, 23, 7, 8, 6, 14, 13, 16, 1, 29, 26, 27, 28, 19, 12
	ROUND3		5, 28, 15, 20, 16, 27, 30, 23, 25, 9, 24, 19, 18, 8, 11, 7, 21, 14, 12, 13, 26, 31, 3, 10, 4, 5, 0, 1, 2, 6, 17, 22, 29, 19, 12, 22, 5, 0, 8, 29, 11, 20, 9, 23, 16, 24, 2, 17, 6, 14, 10, 3, 25, 7, 1, 21, 30, 15, 26, 27, 28, 4, 13
	ROUND3		6, 29, 20, 23, 22, 28, 8, 13, 24, 5, 16, 19, 14, 25, 10, 15, 11, 26, 30, 31, 27, 18, 12, 17, 2, 6, 0, 1, 3, 4, 7, 9, 21, 4, 13, 24, 19, 29, 3, 15, 23, 5, 9, 14, 21, 2, 12, 11, 25, 7, 16, 0, 8, 10, 30, 17, 22, 20, 26, 27, 28, 6, 1
	ROUND3		7, 21, 23, 13, 9, 29, 25, 31, 16, 6, 22, 19, 26, 24, 17, 20, 10, 27, 8, 18, 28, 14, 30, 7, 3, 4, 0, 1, 2, 5, 11, 12, 15, 6, 1, 2, 4, 15, 0, 20, 14, 19, 9, 7, 17, 12, 13, 23, 8, 10, 21, 29, 3, 16, 22, 11, 24, 5, 26, 27, 28, 25, 30
	ROUND3		8, 15, 13, 31, 12, 21, 24, 18, 22, 4, 9, 19, 27, 16, 7, 23, 17, 28, 25, 14, 29, 26, 8, 11, 2, 5, 0, 1, 3, 6, 10, 20, 30, 25, 30, 12, 6, 20, 29, 5, 7, 4, 9, 10, 11, 13, 1, 14, 3, 16, 17, 15, 0, 21, 24, 23, 2, 19, 26, 27, 28, 8, 22
	ROUND3		9, 30, 31, 18, 20, 15, 16, 14, 9, 5, 12, 19, 28, 22, 11, 13, 7, 29, 24, 26, 21, 27, 25, 10, 3, 6, 0, 1, 2, 4, 8, 17, 23, 8, 22, 13, 25, 5, 15, 19, 10, 6, 9, 16, 23, 1, 30, 7, 0, 21, 11, 20, 29, 17, 2, 14, 12, 4, 26, 27, 28, 3, 24
	ROUND3		10, 23, 18, 14, 17, 30, 22, 26, 12, 6, 20, 19, 29, 9, 10, 31, 11, 21, 16, 27, 15, 28, 24, 8, 2, 4, 0, 1, 3, 5, 7, 13, 25, 3, 24, 1, 8, 19, 20, 4, 16, 25, 9, 21, 14, 30, 22, 10, 29, 17, 23, 5, 15, 11, 12, 7, 13, 6, 26, 27, 28, 0, 2
	ROUND3		11, 25, 14, 26, 13, 23, 9, 27, 20, 4, 17, 19, 21, 12, 8, 18, 10, 15, 22, 28, 30, 29, 16, 7, 3, 5, 0, 1, 2, 6, 11, 24, 31, 0, 2, 30, 3, 4, 5, 6, 21, 8, 9, 17, 7, 22, 24, 16, 15, 11, 14, 19, 20, 23, 13, 10, 1, 25, 26, 27, 28, 29, 12
	ROUND3		12, 31, 26, 27, 24, 25, 12, 28, 17, 5, 13, 19, 15, 20, 7, 14, 8, 30, 9, 29, 23, 21, 22, 11, 2, 6, 0, 1, 3, 4, 10, 16, 18, 29, 12, 22, 0, 6, 19, 25, 17, 3, 9, 11, 10, 24, 2, 21, 20, 23, 7, 4, 5, 14, 1, 16, 30, 8, 26, 27, 28, 15, 13
	ROUND3		13, 18, 27, 28, 16, 31, 20, 29, 13, 6, 24, 19, 30, 17, 11, 26, 7, 23, 12, 21, 25, 15, 9, 10, 3, 4, 0, 1, 2, 5, 8, 14, 22, 15, 13, 24, 29, 25, 4, 8, 11, 0, 9, 23, 16, 2, 12, 17, 5, 14, 10, 6, 19, 7, 30, 21, 22, 3, 26, 27, 28, 20, 1
	ROUND3		14, 22, 28, 29, 14, 18, 17, 21, 24, 4, 16, 19, 23, 13, 10, 27, 11, 25, 20, 15, 31, 30, 12, 8, 2, 5, 0, 1, 3, 6, 7, 9, 26, 20, 1, 2, 15, 8, 6, 3, 23, 29, 9, 14, 21, 12, 13, 11, 19, 7, 16, 25, 4, 10, 22, 17, 24, 0, 26, 27, 28, 5, 30
	ROUND3		15, 26, 29, 21, 9, 22, 13, 15, 16, 5, 14, 19, 25, 24, 8, 28, 10, 31, 17, 30, 18, 23, 20, 7, 3, 6, 0, 1, 2, 4, 11, 12, 27, 5, 30, 12, 20, 3, 25, 0, 14, 15, 9, 7, 17, 13, 1, 23, 4, 10, 21, 8, 6, 16, 24, 11, 2, 29, 26, 27, 28, 19, 22
	ROUND3		16, 27, 21, 15, 12, 26, 24, 30, 14, 6, 9, 19, 31, 16, 7, 29, 8, 18, 13, 23, 22, 25, 17, 11, 2, 4, 0, 1, 3, 5, 10, 20, 28, 19, 22, 13, 5, 0, 8, 29, 7, 20, 9, 10, 11, 1, 30, 14, 6, 16, 17, 3, 25, 21, 2, 23, 12, 15, 26, 27, 28, 4, 24
	ROUND3		17, 28, 15, 30, 20, 27, 16, 23, 9, 4, 12, 19, 18, 14, 11, 21, 7, 22, 24, 25, 26, 31, 13, 10, 3, 5, 0, 1, 2, 6, 8, 17, 29, 4, 24, 1, 19, 29, 3, 15, 10, 5, 9, 16, 23, 30, 22, 7, 25, 21, 11, 0, 8, 17, 12, 14, 13, 20, 26, 27, 28, 6, 2
	ROUND3		18, 29, 30, 23, 17, 28, 14, 25, 12, 5, 20, 19, 22, 9, 10, 15, 11, 26, 16, 31, 27, 18, 24, 8, 2, 6, 0, 1, 3, 4, 7, 13, 21, 6, 2, 30, 4, 15, 0, 20, 16, 19, 9, 21, 14, 22, 24, 10, 8, 17, 23, 29, 3, 11, 13, 7, 1, 5, 26, 27, 28, 25, 12
	ROUND3		19, 21, 23, 25, 13, 29, 9, 31, 20, 6, 17, 19, 26, 12, 8, 30, 10, 27, 14, 18, 28, 22, 16, 7, 3, 4, 0, 1, 2, 5, 11, 15, 24, 25, 12, 22, 6, 20, 29, 5, 21, 4, 9, 17, 7, 24, 2, 16, 3, 11, 14, 15, 0, 23, 1, 10, 30, 19, 26, 27, 28, 8, 13
	ROUND3		20, 24, 25, 31, 15, 21, 12, 18, 17, 4, 13, 19, 27, 20, 7, 23, 8, 28, 9, 22, 29, 26, 14, 11, 2, 5, 0, 1, 3, 6, 10, 16, 30, 8, 13, 24, 25, 5, 15, 19, 17, 6, 9, 11, 10, 2, 12, 21, 0, 23, 7, 20, 29, 14, 30, 16, 22, 4, 26, 27, 28, 3, 1
	ROUND3		21, 30, 31, 18, 16, 24, 20, 22, 13, 5, 15, 19, 28, 17, 11, 25, 7, 29, 12, 26, 21, 27, 9, 10, 3, 6, 0, 1, 2, 4, 8, 14, 23, 3, 1, 2, 8, 19, 20, 4, 11, 25, 9, 23, 16, 12, 13, 17, 29, 14, 10, 5, 15, 7, 22, 21, 24, 6, 26, 27, 28, 0, 30
	ROUND3		22, 23, 18, 22, 14, 30, 17, 26, 15, 6, 16, 19, 29, 13, 10, 31, 11, 21, 20, 27, 24, 28, 12, 8, 2, 4, 0, 1, 3, 5, 7, 9, 25, 0, 30, 12, 3, 4, 5, 6, 23, 8, 9, 14, 21, 13, 1, 11, 15, 7, 16, 19, 20, 10, 24, 17, 2, 25, 26, 27, 28, 29, 22
	LAST_ROUND3	22, 9, 23, 13, 25, 22, 26, 9, 23, 13, 27, 16, 4, 14, 19, 21, 15, 8, 18, 10, 24, 17, 28, 30, 29, 20, 7, 3, 5, 0, 1, 2, 6, 11, 12, 31, 29, 22, 13, 0, 6, 19, 25, 14, 3, 9, 7, 17, 1, 30, 23, 20, 10, 21, 4, 5, 16, 2, 11, 12, 8, 26, 27, 28, 15, 24
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
	ldp		x29, x30, [sp], #208
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
