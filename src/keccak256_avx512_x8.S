/*
 * void keccaktree_keccak256_avx512_x8(unsigned char *output,
 *                                     const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 8 at a time: node j
 * of a batch lives in qword lane j of every zmm register. AVX-512F + VL.
 * The rounds are in keccak256_avx512.inc, the frame (loop, tail, Windows ABI)
 * in keccak256_x86_frame.inc. A single node (a whole call or the last
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

#define NODES		8
#define VBYTES		64
#define VR		zmm
#define VREG(n)		VREG_(n)
#define VREG_(n)	zmm##n
#define VMEM(i)		zmmword ptr [r9 + 64*(i)]
#define RC(r)		qword ptr [rip + .LKECCAK_RC + 8*(r)]{1to8}
#define K1		qword ptr [rip + .LK1]{1to8}
#define K63		qword ptr [rip + .LK63]{1to8}
#define ROT8		zmmword ptr [rip + .LROT8]
#define ROT56		zmmword ptr [rip + .LROT56]
#define SMALL_TAIL_X1	keccaktree_keccak256_x86_x1	/* a single node: scalar */
#define SMALL_TAIL	keccaktree_keccak256_avx512vl_x4
#define SMALL_TAIL_MAX	4

#include "keccak256_x86_frame.inc"
#include "keccak256_avx512.inc"

/* digest words o0..o3 (8 nodes each) -> 8 x 32 bytes at [BOUT].
 * o0..o3 can be any registers; once the first four instructions have read
 * them, everything else is free. vpermt2q keeps its index register, so the
 * four index vectors are loaded once: the first level pairs the words of
 * nodes 0..3 (lo) or 4..7 (hi), the second puts the four words of two nodes
 * side by side. */
.macro OUTPUT o0, o1, o2, o3
	vmovdqa64	zmm22, zmmword ptr [rip + .LOUT_LO]
	vmovdqa64	zmm23, zmmword ptr [rip + .LOUT_HI]
	vmovdqa64	zmm24, zmmword ptr [rip + .LOUT_EVEN]
	vmovdqa64	zmm25, zmmword ptr [rip + .LOUT_ODD]
	vmovdqa64	zmm26, VR\o0
	vmovdqa64	zmm27, VR\o2
	vpermt2q	VR\o0, zmm22, VR\o1		/* n0..n3: w0 w1 */
	vpermt2q	VR\o2, zmm22, VR\o3		/* n0..n3: w2 w3 */
	vpermt2q	zmm26, zmm23, VR\o1		/* n4..n7: w0 w1 */
	vpermt2q	zmm27, zmm23, VR\o3		/* n4..n7: w2 w3 */
	vmovdqa64	zmm28, VR\o0
	vmovdqa64	zmm29, zmm26
	vpermt2q	VR\o0, zmm24, VR\o2		/* nodes 0, 1 */
	vpermt2q	zmm28, zmm25, VR\o2		/* nodes 2, 3 */
	vpermt2q	zmm26, zmm24, zmm27		/* nodes 4, 5 */
	vpermt2q	zmm29, zmm25, zmm27		/* nodes 6, 7 */
	vmovdqu64	zmmword ptr [BOUT + 0*64], VR\o0
	vmovdqu64	zmmword ptr [BOUT + 1*64], zmm28
	vmovdqu64	zmmword ptr [BOUT + 2*64], zmm26
	vmovdqu64	zmmword ptr [BOUT + 3*64], zmm29
.endm

.text
.p2align 6
/* one batch: 8 nodes at [BIN] -> 8 digests at [BOUT] */
.Lbatch:
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
	KECCAK_F
	ret

	FUNCTION keccaktree_keccak256_avx512_x8

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
