/*
 * void keccaktree_keccak256_avx2_x9(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 9 at a time: the
 * two alternating 4-node batches of keccak256_avx2_x8 in the vector
 * registers plus one node in the general registers
 * (keccak256_x86_scalar.inc), with the scalar round's instructions spread
 * through the vector rounds. The vector rounds keep the vector pipes busy
 * while the integer ALUs idle; the scalar node uses them, and the front
 * end has the width to feed both. One scalar round (24 rounds of 24) runs
 * during each pair of vector rounds. Needs AVX2, BMI1 and BMI2.
 *
 * Remaining nodes go to keccaktree_keccak256_x86_x1 (1..2), keccaktree_keccak256_avx2_x4
 * (3..4) or a padded batch (5..8); see the tail policy below.
 *
 * Registers: ymm0..15, rsi and the frame's r9 for the vector stream, r10
 * and r11 as the state buffer pointers of a round; rax, rbx, rcx, rdx,
 * rdi, rbp, r8, r12..r15 for the scalar nodes (the frame's rax, rdx, rdi,
 * rbp, r10 and r11 are saved around a batch, the loop count is in
 * memory).
 */
#ifdef __x86_64__
.intel_syntax noprefix

#ifndef NS
#define NS		1			/* scalar nodes per batch */
#endif
#define NODES		(8 + NS)
#define VBYTES		32
#define SLOTS		(2*2112 + 464)
/* Tail policy (keccak256_x86_frame.inc), from the Zen 3 costs of a call
 * right after an x10 batch (ns; the one-round loop body leaves the other
 * kernels in the op cache, so only x8 and x9 still run partly from the
 * decoder): x1 220/node, x2 348, x4 358 (3..4 nodes), x5 455, x8 820,
 * x9 730, a padded x10 batch 660. So after a batch: 1..2 nodes to
 * x86_x1, 3..4 to avx2_x4 (3 padded there), 5 to avx2_x5, 6..9 a padded
 * batch here (x5 and the scalar kernel for 6: 1443 vs 1301 for 16
 * nodes), unless the calibration (keccaktree_avx2_x10_mid_tail) found
 * that avx2_x5 and its tail are faster for 6..9 as well (Gracemont: x5 +
 * x1 for 6 nodes 1210 vs a padded x10 1900).
 * At entry everything is hot and the counts below go whole to the kernel
 * that wins there: 5..6 to avx2_x5 (375, 593 with its x1 tail; the x4
 * chain costs 592, 728), 8 to avx2_x8 (650 vs 660), 12 to x8 + x4 (1022
 * vs x10 + 2 x1 1110) and 16 to two x8 batches (1300 vs x10 + a padded
 * x10 1330). Everything else: 1 and 2 at entry go through avx2_x4 (so 2
 * nodes reach the lane-pair kernel, 356), 7 and 9 are padded batches
 * (660 vs 744 and 870 through x8). */
#define SMALL_TAIL_X1	keccaktree_keccak256_x86_x1
#define SMALL_TAIL_X1_MAX_AFTER	2
#define SMALL_TAIL	keccaktree_keccak256_avx2_x4
#define SMALL_TAIL_MAX	4
#if NS == 2
#define SMALL_TAIL_MID	keccaktree_keccak256_avx2_x5
#define SMALL_TAIL_MID_MAX_VAR	.Lmid_tail_max
#endif
#define ENTRY_ALT	keccaktree_keccak256_avx2_x8
#define ENTRY_ALT_MASK	((1 << 8) | (1 << 12) | (1 << 16))
#define ENTRY_ALT2	keccaktree_keccak256_avx2_x5
#define ENTRY_ALT2_MASK	((1 << 5) | (1 << 6))
#define SAVE_GPRS
#include "keccak256_x86_frame.inc"

#define RCP		rsi			/* round constants (broadcast) */

/* the scalar node: parities / row B, D, temporary */
#define SC0		rax
#define SC1		rbx
#define SC2		rdx
#define SC3		rdi
#define SC4		r8
#define SD0		r12
#define SD1		r13
#define SD2		r14
#define SD3		r15
#define SD4		rbp
#define ST		rcx
/* the state buffers of the current round (block registers, below) */
#define S_IN		r10
#define S_OUT		r11
/* each scalar round stores its parities and the next one's theta reads
 * them (SPAR_MEM): the register roles then stay the same in every round,
 * which the one-round loop body needs; with NS = 2 the nodes also share
 * the registers */
#define SPAR_MEM	1
/* scalar chunks per vector lane hook: a round of 65 chunks over the
 * 110 hooks of a pair of vector rounds (NS = 1) or the 55 of one round
 * (the rest after the round; 1 per hook measured best, 1.2 is 2% slower) */
#ifndef SNUM
#if NS == 1
#define SNUM		3
#define SDEN		5
#else
#define SNUM		1
#define SDEN		1
#endif
#endif
#include "keccak256_x86_scalar.inc"
#include "keccak256_avx2.inc"

/* Frame layout at r9 (= rsp): two blocks, each holding one state buffer
 * of every node (batch A, batch B, the scalar nodes) and the digests of
 * the scalar nodes, then the saved parities of each batch and the saved
 * registers. A round reads one block and writes the other, through the
 * registers S_IN / S_OUT, which swap after every round: the loop body is
 * then one round of each batch (about 4.5 KB) instead of two, half the
 * op-cache footprint, so that a kernel called after a batch of this one
 * (the tail of the remaining nodes, the next tree layer) still runs from
 * the op cache. */
#define BLK		2112
#define SA		0			/* 25 lanes of batch A */
#define SB		800			/* batch B */
#define SS		1600			/* scalar node S: 25 qwords */
#define ST_		1824			/* scalar node T */
#define SOUT		2048			/* scalar digests (32-byte aligned) */
#define BLK0		r9
#define BLK1		r9+BLK
#define PA		r9+2*BLK
#define PB		r9+2*BLK+160
#define SAVE_RAX	(2*BLK + 320)
#define SAVE_RDX	(2*BLK + 328)
#define SAVE_RDI	(2*BLK + 336)
#define SAVE_RBP	(2*BLK + 344)
#define SAVE_BIN	(2*BLK + 352)
#define SAVE_BOUT	(2*BLK + 360)
#define SCNT		(2*BLK + 368)
#define SPARS		(2*BLK + 384)		/* saved parities of S and T */
#define SPART		(2*BLK + 424)

.text
.p2align 6
/* one batch: NODES nodes at [BIN] -> NODES digests at [BOUT] */
.Lbatch:
	mov		qword ptr [r9 + SAVE_RAX], rax
	mov		qword ptr [r9 + SAVE_RDX], rdx
	mov		qword ptr [r9 + SAVE_RDI], rdi
	mov		qword ptr [r9 + SAVE_RBP], rbp
	mov		qword ptr [r9 + SAVE_BIN], BIN
	mov		qword ptr [r9 + SAVE_BOUT], BOUT
	lea		RCP, [rip + .LRC4]
	/* the scalar nodes' data words to their state buffers */
	vmovdqu		ymm0, ymmword ptr [BIN + 8*64]
	vmovdqu		ymm1, ymmword ptr [BIN + 8*64 + 32]
	vmovdqa		ymmword ptr [r9 + SS], ymm0
	vmovdqa		ymmword ptr [r9 + SS + 32], ymm1
.if NS == 2
	vmovdqu		ymm0, ymmword ptr [BIN + 9*64]
	vmovdqu		ymm1, ymmword ptr [BIN + 9*64 + 32]
	vmovdqa		ymmword ptr [r9 + ST_], ymm0
	vmovdqa		ymmword ptr [r9 + ST_ + 32], ymm1
.endif

	/* round 0: block 0 -> block 1 */
	SROUND_BEGIN	0, SS, BLK + SS, 0, 0, SPARS
	LOAD		BIN
	ROUND0		BLK0+SA, BLK1+SA
	STORE_C		PA
.if NS == 2
	SFLUSH
	SROUND_BEGIN	0, ST_, BLK + ST_, 0, 0, SPART
.endif
	LOAD		BIN+4*64
	ROUND0		BLK0+SB, BLK1+SB
	STORE_C		PB
	SFLUSH
	THETA		PA

	/* rounds 1..22 from the block at S_IN to the one at S_OUT, batch A
	 * then batch B; each round leaves the other batch's theta in
	 * D0..D4 */
	lea		S_IN, [BLK1]
	mov		S_OUT, r9
	mov		qword ptr [r9 + SCNT], 22
1:
	SROUND_BEGIN	1, SS, SS, 32, 0, SPARS, 1
	ROUND		S_IN+SA, S_OUT+SA, 32, PB
	STORE_C		PA
.if NS == 2
	SFLUSH
	SROUND_BEGIN	1, ST_, ST_, 32, 0, SPART, 1
.endif
	ROUND		S_IN+SB, S_OUT+SB, 32, PA
	STORE_C		PB
	SFLUSH
	add		RCP, 32
	xchg		S_IN, S_OUT
	dec		qword ptr [r9 + SCNT]
	jnz		1b

	/* round 23: block 1 -> the digests */
	SROUND_BEGIN	23, BLK + SS, SOUT, 32, 0, SPARS
	ROUND23		BLK1+SA, 32, D
	SFLUSH
	mov		BOUT, qword ptr [r9 + SAVE_BOUT]
	OUTPUT		BOUT
	THETA		PB
.if NS == 2
	SROUND_BEGIN	23, BLK + ST_, SOUT + 32, 32, 0, SPART
.endif
	ROUND23		BLK1+SB, 32, D
	SFLUSH
	mov		BOUT, qword ptr [r9 + SAVE_BOUT]
	OUTPUT		BOUT+4*32
	vmovdqu		ymm0, ymmword ptr [r9 + SOUT]
	vmovdqu		ymmword ptr [BOUT + 8*32], ymm0
.if NS == 2
	vmovdqu		ymm1, ymmword ptr [r9 + SOUT + 32]
	vmovdqu		ymmword ptr [BOUT + 9*32], ymm1
.endif
	mov		BIN, qword ptr [r9 + SAVE_BIN]
	mov		rax, qword ptr [r9 + SAVE_RAX]
	mov		rdx, qword ptr [r9 + SAVE_RDX]
	mov		rdi, qword ptr [r9 + SAVE_RDI]
	mov		rbp, qword ptr [r9 + SAVE_RBP]
	ret

#if NS == 1
	FUNCTION keccaktree_keccak256_avx2_x9
#else
	FUNCTION keccaktree_keccak256_avx2_x10

/* void keccaktree_avx2_x10_mid_tail(uint64_t max): after an x10 batch,
 * 5..max remaining nodes go to keccaktree_keccak256_avx2_x5 (and its
 * tail), more to a padded x10 batch; max = 4 pads 5..9 (the default;
 * keccaktree_detect sets 5 or 9) */
.data
.p2align 3
.Lmid_tail_max:
	.quad 4
.text
.p2align 4
.globl keccaktree_avx2_x10_mid_tail
#ifndef _WIN64
.type keccaktree_avx2_x10_mid_tail,%function
#endif
keccaktree_avx2_x10_mid_tail:
	mov		qword ptr [rip + .Lmid_tail_max], ARG_OUT
	ret
#ifndef _WIN64
.size keccaktree_avx2_x10_mid_tail, .-keccaktree_avx2_x10_mid_tail
#endif
#endif
	AVX2_RODATA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
