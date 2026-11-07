/*
 * void keccaktree_keccak256_avx512_x8(unsigned char *output,
 *                                     const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 8 at a time: node j
 * of a batch lives in qword lane j of every zmm register. AVX-512F + VL.
 * The rounds are in keccak256_avx512.inc (or, with KT_DFORM defined by
 * keccak256_avx512_x8d.S, the all-in-registers rounds of
 * keccak256_avx512d.inc), the frame (loop, tail, Windows ABI) in
 * keccak256_x86_frame.inc. A single node (a whole call or the last
 * one) goes to keccaktree_keccak256_x86_x1 (BMI1 + BMI2, which every
 * AVX-512 core has: keccaktree_detect checks), 2..4 remaining nodes to the
 * ymm kernel, which takes the same time for them; 5..7 are padded to a
 * batch.
 *
 * The transposes between batches matter more than their size suggests: the
 * shuffles run on port 5 only, and while the next batch waits for its
 * input, port 0 has nothing to do. So the input transpose does its first
 * level in the load unit and the output transpose is two levels of vpermt2q
 * instead of three of unpack/shuffle.
 */
#ifdef __x86_64__
.intel_syntax noprefix

/* With NS defined (keccak256_avx512_x9.S, keccak256_avx512_x9d.S: NS = 1)
 * the batch also hashes NS nodes in the general registers
 * (keccak256_x86_scalar.inc), their round chunks spread through the vector
 * round by VHOOK; see that file. The including file may also set
 * KERNEL_NAME, SMALL_TAIL (the kernel for 2..4 remaining nodes) and
 * ENTRY_ALT (the zmm kernel whole calls of 8..56 nodes go to). */
#ifdef NS
#define NODES		(8 + NS)
#define SLOTS		(10*64 + NS*448 + 64 + 64)
#define SAVE_GPRS
#else
#define NODES		8
#define SLOTS		(10*64 + 64)
#endif
#define VBYTES		64
#define VR		zmm
#define VREG(n)		VREG_(n)
#define VREG_(n)	zmm##n
#define VMEM(i)		zmmword ptr [r9 + 64*(i)]
#define RC(r)		qword ptr [rip + .LKECCAK_RC + 8*(r)]{1to8}
#define K1		qword ptr [rip + .LK1]{1to8}
#define K63		qword ptr [rip + .LK63]{1to8}
#define RCP		r8
#define RCL(k)		qword ptr [RCP + 8*(k)]{1to8}
#define ROT8		zmmword ptr [rip + .LROT8]
#define ROT56		zmmword ptr [rip + .LROT56]
#ifndef KERNEL_NAME
#define KERNEL_NAME	keccaktree_keccak256_avx512_x8
#endif
#define SMALL_TAIL_X1	keccaktree_keccak256_x86_x1	/* a single node: scalar */
#ifndef SMALL_TAIL
#define SMALL_TAIL	keccaktree_keccak256_avx512vl_x4
#endif
#define SMALL_TAIL_MAX	4
#ifdef NS
/* whole calls of a multiple of 8 nodes (below 64) go to the zmm kernel:
 * a padded batch here costs as much as a full one */
#ifndef ENTRY_ALT
#define ENTRY_ALT	keccaktree_keccak256_avx512_x8
#endif
#define ENTRY_ALT_MASK	((1 << 8) | (1 << 16) | (1 << 24) | (1 << 32) | (1ULL << 40) | (1ULL << 48) | (1ULL << 56))
#endif

#include "keccak256_x86_frame.inc"

#ifdef NS
/* the scalar node: parities / row B, D, temporary; RCP (r8) is shared
 * with the vector loop, whose count lives in memory */
#define SC0		rax
#define SC1		rbx
#define SC2		rdx
#define SC3		rdi
#define SC4		rsi
#define SD0		r12
#define SD1		r13
#define SD2		r14
#define SD3		r15
#define SD4		rbp
#define ST		rcx
#define SPAR_MEM	0
/* 65 scalar chunks over the 55 hooks of a vector round */
#ifndef SNUM
#define SNUM		6
#define SDEN		5
#endif
#include "keccak256_x86_scalar.inc"
/* frame layout at r9 (= rsp) after the vector slots: the two scalar
 * state buffers, the scalar digest, the saved registers, the loop count */
#define SS0		(10*64)
#define SS1		(10*64 + 224)
#define SOUT		(10*64 + 448)
#define SAVE_RAX	(SOUT + 64)
#define SAVE_RDX	(SOUT + 72)
#define SAVE_RDI	(SOUT + 80)
#define SAVE_RBP	(SOUT + 88)
#define LOOP_CNT	r9 + SOUT + 96
/* the scalar round of each vector round: round k reads buffer k&1 and
 * writes the other; the parities start in SC (even rounds) or SD (odd);
 * the constant is at [RCP + 8*(k - first round of the stretch)] */
#define RHOOK_DEFINED
.macro RHOOK_BEGIN k
.if \k == 0
	SROUND_BEGIN	0, SS0, SS1, 0, 0
.elseif \k == 23
	SROUND_BEGIN	23, SS1, SOUT, 16, 1
.elseif \k >= 21
.if \k & 1
	SROUND_BEGIN	1, SS1, SS0, 8*(\k - 21), 1
.else
	SROUND_BEGIN	1, SS0, SS1, 8*(\k - 21), 0
.endif
.elseif \k & 1
	SROUND_BEGIN	1, SS1, SS0, 8*(\k - 1), 1
.else
	SROUND_BEGIN	1, SS0, SS1, 8*(\k - 1), 0
.endif
.endm
.macro RHOOK_END
	SFLUSH
.endm
#else
#define LOOP_CNT	r9 + 10*64
#endif

#ifdef KT_DFORM
#include "keccak256_avx512d.inc"
#else
#include "keccak256_avx512.inc"
#endif

/* digest words o0..o3 (8 nodes each) -> 8 x 32 bytes at [BOUT], with the
 * scratch registers s0..s7 (any eight others; the rounds of
 * keccak256_avx512.inc leave their digest in registers below 22, the
 * D-form rounds pass eight dead ones). vpermt2q keeps its index register,
 * so the four index vectors are loaded once: the first level pairs the
 * words of nodes 0..3 (lo) or 4..7 (hi), the second puts the four words of
 * two nodes side by side. */
.macro OUTPUT o0, o1, o2, o3, s0=22, s1=23, s2=24, s3=25, s4=26, s5=27, s6=28, s7=29
	vmovdqa64	VR\s0, zmmword ptr [rip + .LOUT_LO]
	vmovdqa64	VR\s1, zmmword ptr [rip + .LOUT_HI]
	vmovdqa64	VR\s2, zmmword ptr [rip + .LOUT_EVEN]
	vmovdqa64	VR\s3, zmmword ptr [rip + .LOUT_ODD]
	vmovdqa64	VR\s4, VR\o0
	vmovdqa64	VR\s5, VR\o2
	vpermt2q	VR\o0, VR\s0, VR\o1		/* n0..n3: w0 w1 */
	vpermt2q	VR\o2, VR\s0, VR\o3		/* n0..n3: w2 w3 */
	vpermt2q	VR\s4, VR\s1, VR\o1		/* n4..n7: w0 w1 */
	vpermt2q	VR\s5, VR\s1, VR\o3		/* n4..n7: w2 w3 */
	vmovdqa64	VR\s6, VR\o0
	vmovdqa64	VR\s7, VR\s4
	vpermt2q	VR\o0, VR\s2, VR\o2		/* nodes 0, 1 */
	vpermt2q	VR\s6, VR\s3, VR\o2		/* nodes 2, 3 */
	vpermt2q	VR\s4, VR\s2, VR\s5		/* nodes 4, 5 */
	vpermt2q	VR\s7, VR\s3, VR\s5		/* nodes 6, 7 */
	vmovdqu64	zmmword ptr [BOUT + 0*64], VR\o0
	vmovdqu64	zmmword ptr [BOUT + 1*64], VR\s6
	vmovdqu64	zmmword ptr [BOUT + 2*64], VR\s4
	vmovdqu64	zmmword ptr [BOUT + 3*64], VR\s7
.endm

.text
.p2align 6
/* one batch: NODES nodes at [BIN] -> NODES digests at [BOUT] */
.Lbatch:
#ifdef NS
	mov		qword ptr [r9 + SAVE_RAX], rax
	mov		qword ptr [r9 + SAVE_RDX], rdx
	mov		qword ptr [r9 + SAVE_RDI], rdi
	mov		qword ptr [r9 + SAVE_RBP], rbp
	/* the scalar node's data words to its state buffer */
	vmovdqu		ymm0, ymmword ptr [BIN + 8*64]
	vmovdqu		ymm1, ymmword ptr [BIN + 8*64 + 32]
	vmovdqa		ymmword ptr [r9 + SS0], ymm0
	vmovdqa		ymmword ptr [r9 + SS0 + 32], ymm1
#endif
	/* 8x8 qword transpose: VREG(j) = word j of nodes 0..7. The first
	 * level interleaves node pairs in the load unit: a load of node 2i and
	 * a merge-masked load of node 2i+1 shifted by one qword (k1 = odd
	 * lanes) give the same as vpunpck{l,h}qdq would; the merge is an ALU
	 * op, but one that can take either port. Two shuffle levels follow. */
	kmovw		k1, word ptr [rip + .LODD]
	vmovdqu64	zmm16, zmmword ptr [BIN + 0*64]		/* n0 w0 w2 w4 w6 */
	vmovdqu64	zmm16{k1}, zmmword ptr [BIN + 1*64 - 8]	/* n1 w0 w2 w4 w6 */
	vmovdqu64	zmm17, zmmword ptr [BIN + 0*64 + 8]	/* n0 w1 w3 w5 w7 */
	vmovdqu64	zmm17{k1}, zmmword ptr [BIN + 1*64]	/* n1 w1 w3 w5 w7 */
	vmovdqu64	zmm18, zmmword ptr [BIN + 2*64]
	vmovdqu64	zmm18{k1}, zmmword ptr [BIN + 3*64 - 8]
	vmovdqu64	zmm19, zmmword ptr [BIN + 2*64 + 8]
	vmovdqu64	zmm19{k1}, zmmword ptr [BIN + 3*64]
	vmovdqu64	zmm20, zmmword ptr [BIN + 4*64]
	vmovdqu64	zmm20{k1}, zmmword ptr [BIN + 5*64 - 8]
	vmovdqu64	zmm21, zmmword ptr [BIN + 4*64 + 8]
	vmovdqu64	zmm21{k1}, zmmword ptr [BIN + 5*64]
	vmovdqu64	zmm22, zmmword ptr [BIN + 6*64]
	vmovdqu64	zmm22{k1}, zmmword ptr [BIN + 7*64 - 8]
	vmovdqu64	zmm23, zmmword ptr [BIN + 6*64 + 8]
	vmovdqu64	zmm23{k1}, zmmword ptr [BIN + 7*64]
	vshufi64x2	zmm8,  zmm16, zmm18, 0x88		/* n0..n3: w0, w4 */
	vshufi64x2	zmm9,  zmm16, zmm18, 0xDD		/* n0..n3: w2, w6 */
	vshufi64x2	zmm10, zmm17, zmm19, 0x88		/* n0..n3: w1, w5 */
	vshufi64x2	zmm11, zmm17, zmm19, 0xDD		/* n0..n3: w3, w7 */
	vshufi64x2	zmm12, zmm20, zmm22, 0x88		/* n4..n7 */
	vshufi64x2	zmm13, zmm20, zmm22, 0xDD
	vshufi64x2	zmm14, zmm21, zmm23, 0x88
	vshufi64x2	zmm15, zmm21, zmm23, 0xDD
	vshufi64x2	zmm0, zmm8,  zmm12, 0x88
	vshufi64x2	zmm4, zmm8,  zmm12, 0xDD
	vshufi64x2	zmm2, zmm9,  zmm13, 0x88
	vshufi64x2	zmm6, zmm9,  zmm13, 0xDD
	vshufi64x2	zmm1, zmm10, zmm14, 0x88
	vshufi64x2	zmm5, zmm10, zmm14, 0xDD
	vshufi64x2	zmm3, zmm11, zmm15, 0x88
	vshufi64x2	zmm7, zmm11, zmm15, 0xDD
#if defined(KT_DFORM) && defined(KT_AVX512_UNROLLED)
	KECCAK_F_D
#elif defined(KT_DFORM)
	KECCAK_F_D_LOOP
#elif defined(KT_AVX512_UNROLLED) && !defined(NS)
	KECCAK_F
#else
	KECCAK_F_LOOP
#endif
#ifdef NS
	vmovdqu		ymm0, ymmword ptr [r9 + SOUT]
	vmovdqu		ymmword ptr [BOUT + 8*32], ymm0
	mov		rax, qword ptr [r9 + SAVE_RAX]
	mov		rdx, qword ptr [r9 + SAVE_RDX]
	mov		rdi, qword ptr [r9 + SAVE_RDI]
	mov		rbp, qword ptr [r9 + SAVE_RBP]
#endif
	ret

	FUNCTION KERNEL_NAME

	KECCAK_RODATA
.p2align 6
.LOUT_LO:	.quad 0, 8, 1, 9, 2, 10, 3, 11
.LOUT_HI:	.quad 4, 12, 5, 13, 6, 14, 7, 15
.LOUT_EVEN:	.quad 0, 1, 8, 9, 2, 3, 10, 11
.LOUT_ODD:	.quad 4, 5, 12, 13, 6, 7, 14, 15
.LROT8:		.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
		.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
		.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
		.byte 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14
.LROT56:	.byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8
		.byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8
		.byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8
		.byte 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8
.LODD:		.word 0xAA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
