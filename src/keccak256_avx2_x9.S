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
 * Registers: ymm0..15, rsi and the frame's r9..r11 for the vector stream;
 * rax, rbx, rcx, rdx, rdi, rbp, r8, r12..r15 for the scalar node (the
 * frame's rax, rdx, rdi and rbp are saved around a batch, the loop count
 * is in memory).
 */
#ifdef __x86_64__
.intel_syntax noprefix

#ifndef NS
#define NS		1			/* scalar nodes per batch */
#endif
#define NODES		(8 + NS)
#define VBYTES		32
#define SLOTS		(110*32 + 448*NS + 64 + 48 + 80)
/* Tail policy (keccak256_x86_frame.inc), from the Zen 3 costs of a call
 * right after an x10 batch, when only x10 and the small scalar kernel are
 * in the op cache (ns): x1 220/node, x2 566, x4 602 (3..4 nodes), x5 638,
 * x8 1000, x9 1070, a padded x10 batch 683. So after a batch: 1..2 nodes
 * to x86_x1, 3..4 to avx2_x4 (3 padded there), 5..9 a padded batch here,
 * unless the calibration (keccaktree_avx2_x10_mid_tail) found that avx2_x5
 * and its tail are faster for 5..9 (Gracemont: x5 + x1 for 6 nodes 1210
 * vs a padded x10 1900; on Zen 3, 858 vs 683).
 * At entry everything is hot and the counts below go whole to the kernel
 * that wins there: 5..6 to avx2_x5 (378, 598 with its x1 tail; the x4
 * chain costs 592, 728), 8 to avx2_x8 (650 vs 683), 12 to x8 + x4 (1022
 * vs x10 + 2 x1 1108) and 16 to two x8 batches (1300 vs x10 + a padded
 * x10 1351). Everything else: 1 and 2 at entry go through avx2_x4 (so 2
 * nodes reach the lane-pair kernel, 356), 7 and 9 are padded batches
 * (683 vs 744 and 870 through x8). */
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
/* scalar chunks per vector lane hook: a round of 65 chunks over the
 * 110 hooks of a pair of vector rounds (NS = 1) or the 55 of one round
 * (the rest after the round; 1 per hook measured best, 1.2 is 2% slower) */
#if NS == 1
#define SPAR_MEM	0
#ifndef SNUM
#define SNUM		3
#define SDEN		5
#endif
#else
#define SPAR_MEM	1			/* the nodes share the registers */
#ifndef SNUM
#define SNUM		1
#define SDEN		1
#endif
#endif
#include "keccak256_x86_scalar.inc"
#include "keccak256_avx2.inc"

/* frame layout at r9 (= rsp): the two state buffers of each vector batch,
 * the saved parities of each batch, the two state buffers of each scalar
 * node, the scalar digests and the saved registers */
#define SA0		r9
#define SA1		r9+25*32
#define SB0		r9+50*32
#define SB1		r9+75*32
#define PA		r9+100*32
#define PB		r9+105*32
#define SS0		(110*32)
#define SS1		(110*32 + 224)
#define ST0		(110*32 + 448)
#define ST1		(110*32 + 672)
#define SOUT		(110*32 + 448*NS)
#define SAVE_RAX	(SOUT + 64)
#define SAVE_RDX	(SOUT + 72)
#define SAVE_RDI	(SOUT + 80)
#define SAVE_RBP	(SOUT + 88)
#define SCNT		(SOUT + 96)
#define SPARS		(SOUT + 104)		/* saved parities (SPAR_MEM) */
#define SPART		(SOUT + 144)

.text
.p2align 6
/* one batch: NODES nodes at [BIN] -> NODES digests at [BOUT] */
.Lbatch:
	mov		qword ptr [r9 + SAVE_RAX], rax
	mov		qword ptr [r9 + SAVE_RDX], rdx
	mov		qword ptr [r9 + SAVE_RDI], rdi
	mov		qword ptr [r9 + SAVE_RBP], rbp
	lea		RCP, [rip + .LRC4]
	/* the scalar nodes' data words to their state buffers */
	vmovdqu		ymm0, ymmword ptr [BIN + 8*64]
	vmovdqu		ymm1, ymmword ptr [BIN + 8*64 + 32]
	vmovdqa		ymmword ptr [r9 + SS0], ymm0
	vmovdqa		ymmword ptr [r9 + SS0 + 32], ymm1
.if NS == 2
	vmovdqu		ymm0, ymmword ptr [BIN + 9*64]
	vmovdqu		ymm1, ymmword ptr [BIN + 9*64 + 32]
	vmovdqa		ymmword ptr [r9 + ST0], ymm0
	vmovdqa		ymmword ptr [r9 + ST0 + 32], ymm1
.endif

	SROUND_BEGIN	0, SS0, SS1, 0, 0, SPARS
	LOAD		BIN
	ROUND0		SA1, SA0
	STORE_C		PA
.if NS == 2
	SFLUSH
	SROUND_BEGIN	0, ST0, ST1, 0, 0, SPART
.endif
	LOAD		BIN+4*64
	ROUND0		SB1, SB0
	STORE_C		PB
	SFLUSH
	THETA		PA

	/* rounds 1..22, two per iteration, batch A then batch B; each round
	 * leaves the other batch's theta in D0..D4 */
	mov		qword ptr [r9 + SCNT], 11
1:
	SROUND_BEGIN	1, SS1, SS0, 32, 1, SPARS
	ROUND		SA0, SA1, 32, PB
	STORE_C		PA
.if NS == 2
	SFLUSH
	SROUND_BEGIN	1, ST1, ST0, 32, 1, SPART
.endif
	ROUND		SB0, SB1, 32, PA
	STORE_C		PB
	SFLUSH
	SROUND_BEGIN	1, SS0, SS1, 64, 0, SPARS
	ROUND		SA1, SA0, 64, PB
	STORE_C		PA
.if NS == 2
	SFLUSH
	SROUND_BEGIN	1, ST0, ST1, 64, 0, SPART
.endif
	ROUND		SB1, SB0, 64, PA
	STORE_C		PB
	SFLUSH
	add		RCP, 64
	dec		qword ptr [r9 + SCNT]
	jnz		1b

	SROUND_BEGIN	23, SS1, SOUT, 32, 1, SPARS
	ROUND23		SA0, 32, D
	OUTPUT		BOUT
	THETA		PB
.if NS == 2
	SFLUSH
	SROUND_BEGIN	23, ST1, SOUT + 32, 32, 1, SPART
.endif
	ROUND23		SB0, 32, D
	OUTPUT		BOUT+4*32
	SFLUSH
	vmovdqu		ymm0, ymmword ptr [r9 + SOUT]
	vmovdqu		ymmword ptr [BOUT + 8*32], ymm0
.if NS == 2
	vmovdqu		ymm1, ymmword ptr [r9 + SOUT + 32]
	vmovdqu		ymmword ptr [BOUT + 9*32], ymm1
.endif
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
 * tail), more to a padded x10 batch; max = 4 pads 5..9 */
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
