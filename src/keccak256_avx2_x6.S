/*
 * void keccaktree_keccak256_avx2_x6(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 6 at a time: the
 * 4-node batch of keccak256_avx2_x4 in the vector registers plus two
 * nodes in the general registers (keccak256_x86_scalar.inc), like
 * keccak256_avx2_x5 with a second scalar node. The two scalar rounds
 * share the eleven registers: the chunks of node S's round come first,
 * those of node T's follow (SROUND_QUEUE), 130 chunks over the 55 lane
 * hooks of one vector round, so each round stores its parities (SPAR_MEM)
 * and the register roles are the same in every round. Needs AVX2, BMI1
 * and BMI2.
 *
 * Made for Gracemont (Alder Lake E-core), whose 256-bit ops run double-
 * pumped on three 128-bit vector pipes while its four integer ALUs idle:
 * the vector round is pipe-bound (184 x 2 pipe-uops / 3 = 123 cycles,
 * 127 measured) and one scalar node per batch is free (avx2_x5: 1.28x
 * avx2_x4). The second is not quite: allocation is 5 uops per cycle with
 * a ymm op taking two slots, so a round costs 184 x 2 + 25 stores + 28
 * loads = 421 slots plus 161 per scalar node: x5 = 582 (116 cycles, still
 * pipe-bound), x6 = 743 (149 cycles, allocation-bound; 146 measured).
 * Measured: 183 ns/node against 188 for avx2_x5 and 240 for avx2_x4
 * (1.025x / 1.31x at 64..1024 nodes); the chunk pacing does not matter
 * (2.0..3.0 per hook within 0.7%). On Golden Cove the scalar ops take
 * the vector ports (0.72x of avx2_x4), on Zen 3 avx2_x10 wins (x6 0.77x
 * of it); the calibration picks.
 *
 * Tail (Gracemont costs per node: a batch here 183 ns, avx2_x5 188, avx2_x4
 * 239, a padded x4 batch of 3 nodes 320, x86_x1 278): a single remaining
 * node goes to keccaktree_keccak256_x86_x1, 2..4 to
 * keccaktree_keccak256_avx2_x4, 5 to keccaktree_keccak256_avx2_x5. When 9,
 * 10, 14, 15 or 20 nodes remain (before a batch, BATCH_ALT_MASK) they go
 * to avx2_x5 as well: 5 + 4, 5 + 5, 5 + 5 + 4, 5 + 5 + 5 and 5 x 4 beat a
 * batch here and the x4 tail of the rest (14 nodes: 202 vs 210 ns/node,
 * 16: 186 vs 197, 20: 187 vs 202; 64 and up end in 6 x 9 + 10 -> x5 x 2).
 * The other remainders stay: 7 = 6 + 1 (197 vs 241 through x5), 8 =
 * 6 + 2 (231 vs 237), 11 = 6 + 5, 13 = 6 + 6 + 1 (190 vs 218). Whole
 * calls of 5, 9, 10, 14, 15 and 20 nodes go to avx2_x5 before the
 * prologue.
 *
 * Registers: ymm0..15, rsi and the frame's r9..r11 for the vector stream;
 * rax, rbx, rcx, rdx, rdi, rbp, r8, r12..r15 for the scalar nodes.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#define NODES		6
#define VBYTES		32
#define SLOTS		2688
#define SMALL_TAIL_X1	keccaktree_keccak256_x86_x1	/* a single node: scalar directly */
#define SMALL_TAIL	keccaktree_keccak256_avx2_x4	/* 2..4 nodes */
#define SMALL_TAIL_MAX	4
#define SMALL_TAIL_MID	keccaktree_keccak256_avx2_x5	/* 5 nodes */
#define SMALL_TAIL_MID_MASK	(1 << 5)
#define BATCH_ALT_MASK	((1 << 9) | (1 << 10) | (1 << 14) | (1 << 15) | (1 << 20))
#define ENTRY_ALT	keccaktree_keccak256_avx2_x5
#define ENTRY_ALT_MASK	((1 << 5) | (1 << 9) | (1 << 10) | (1 << 14) | (1 << 15) | (1 << 20))
#define SAVE_GPRS
#include "keccak256_x86_frame.inc"

#define RCP		rsi			/* round constants (broadcast) */

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
#define SPAR_MEM	1
/* 130 scalar chunks over the 55 hooks of a vector round */
#ifndef SNUM
#define SNUM		12
#define SDEN		5
#endif
#include "keccak256_x86_scalar.inc"
#include "keccak256_avx2.inc"

/* frame layout at r9 (= rsp): the two vector state buffers, the two
 * state buffers of each scalar node, their digests, the saved registers,
 * the loop count and the saved parities of each scalar node */
#define BUF0		r9
#define BUF1		r9+25*32
#define SS0		1600
#define SS1		1824
#define TS0		2048
#define TS1		2272
#define SOUT		2496
#define SAVE_RAX	2560
#define SAVE_RDX	2568
#define SAVE_RDI	2576
#define SAVE_RBP	2584
#define SCNT		2592
#define SPARS		2600
#define SPART		2640

.text
.p2align 6
/* one batch: 6 nodes at [BIN] -> 6 digests at [BOUT] */
.Lbatch:
	mov		qword ptr [r9 + SAVE_RAX], rax
	mov		qword ptr [r9 + SAVE_RDX], rdx
	mov		qword ptr [r9 + SAVE_RDI], rdi
	mov		qword ptr [r9 + SAVE_RBP], rbp
	lea		RCP, [rip + .LRC4]
	vmovdqu		ymm0, ymmword ptr [BIN + 4*64]
	vmovdqu		ymm1, ymmword ptr [BIN + 4*64 + 32]
	vmovdqu		ymm2, ymmword ptr [BIN + 5*64]
	vmovdqu		ymm3, ymmword ptr [BIN + 5*64 + 32]
	vmovdqa		ymmword ptr [r9 + SS0], ymm0
	vmovdqa		ymmword ptr [r9 + SS0 + 32], ymm1
	vmovdqa		ymmword ptr [r9 + TS0], ymm2
	vmovdqa		ymmword ptr [r9 + TS0 + 32], ymm3

	SROUND_BEGIN	0, SS0, SS1, 0, 0, SPARS
	SROUND_QUEUE	0, TS0, TS1, 0, 0, SPART
	LOAD		BIN
	ROUND0		BUF1, BUF0
	SFLUSH

	/* rounds 1..22, two per iteration */
	mov		qword ptr [r9 + SCNT], 11
1:
	SROUND_BEGIN	1, SS1, SS0, 32, 0, SPARS
	SROUND_QUEUE	1, TS1, TS0, 32, 0, SPART
	ROUNDP		BUF0, BUF1, 32
	SFLUSH
	SROUND_BEGIN	1, SS0, SS1, 64, 0, SPARS
	SROUND_QUEUE	1, TS0, TS1, 64, 0, SPART
	ROUNDP		BUF1, BUF0, 64
	SFLUSH
	add		RCP, 64
	dec		qword ptr [r9 + SCNT]
	jnz		1b

	SROUND_BEGIN	23, SS1, SOUT, 32, 0, SPARS
	SROUND_QUEUE	23, TS1, SOUT + 32, 32, 0, SPART
	ROUND23		BUF0, 32
	OUTPUT		BOUT
	SFLUSH
	vmovdqu		ymm0, ymmword ptr [r9 + SOUT]
	vmovdqu		ymm1, ymmword ptr [r9 + SOUT + 32]
	vmovdqu		ymmword ptr [BOUT + 4*32], ymm0
	vmovdqu		ymmword ptr [BOUT + 5*32], ymm1
	mov		rax, qword ptr [r9 + SAVE_RAX]
	mov		rdx, qword ptr [r9 + SAVE_RDX]
	mov		rdi, qword ptr [r9 + SAVE_RDI]
	mov		rbp, qword ptr [r9 + SAVE_RBP]
	ret

	FUNCTION keccaktree_keccak256_avx2_x6
	AVX2_RODATA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
