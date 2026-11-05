/*
 * void keccaktree_keccak256_avx512_x8(unsigned char *output,
 *                                     const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 8 at a time: node j
 * of a batch lives in qword lane j of every zmm register. AVX-512F + VL.
 * The rounds are in keccak256_avx512.inc, the frame (loop, tail, Windows ABI)
 * in keccak256_x86_frame.inc. 1..4 remaining nodes go to the ymm kernel,
 * which takes the same time for them; 5..7 are padded to a batch.
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
#define SMALL_TAIL	keccaktree_keccak256_avx512vl_x4
#define SMALL_TAIL_MAX	4

#include "keccak256_x86_frame.inc"
#include "keccak256_avx512.inc"

/* digest words o0..o3 (8 nodes each) -> 8 x 32 bytes at [BOUT].
 * o0..o3 can be any registers; once the first four instructions have read
 * them, everything else is free. */
.macro OUTPUT o0, o1, o2, o3
	vpunpcklqdq	zmm25, VR\o0, VR\o1			/* n0,n2,n4,n6: w0 w1 */
	vpunpckhqdq	zmm26, VR\o0, VR\o1			/* n1,n3,n5,n7: w0 w1 */
	vpunpcklqdq	zmm27, VR\o2, VR\o3			/* n0,n2,n4,n6: w2 w3 */
	vpunpckhqdq	zmm28, VR\o2, VR\o3			/* n1,n3,n5,n7: w2 w3 */
	vmovdqa64	zmm4, zmmword ptr [rip + .LOUT_LO]
	vmovdqa64	zmm5, zmmword ptr [rip + .LOUT_HI]
	vmovdqa64	zmm0, zmm25
	vpermt2q	zmm0, zmm4, zmm27		/* nodes 0, 2 */
	vmovdqa64	zmm1, zmm26
	vpermt2q	zmm1, zmm4, zmm28		/* nodes 1, 3 */
	vpermt2q	zmm25, zmm5, zmm27		/* nodes 4, 6 */
	vpermt2q	zmm26, zmm5, zmm28		/* nodes 5, 7 */
	vshufi64x2	zmm2, zmm0, zmm1, 0x44		/* nodes 0, 1 */
	vshufi64x2	zmm3, zmm0, zmm1, 0xEE		/* nodes 2, 3 */
	vshufi64x2	zmm4, zmm25, zmm26, 0x44	/* nodes 4, 5 */
	vshufi64x2	zmm5, zmm25, zmm26, 0xEE	/* nodes 6, 7 */
	vmovdqu64	zmmword ptr [BOUT + 0*64], zmm2
	vmovdqu64	zmmword ptr [BOUT + 1*64], zmm3
	vmovdqu64	zmmword ptr [BOUT + 2*64], zmm4
	vmovdqu64	zmmword ptr [BOUT + 3*64], zmm5
.endm

.text
.p2align 6
/* one batch: 8 nodes at [BIN] -> 8 digests at [BOUT] */
.Lbatch:
	/* 8x8 qword transpose: VREG(j) = word j of nodes 0..7 */
	vmovdqu64	zmm8,  zmmword ptr [BIN + 0*64]
	vmovdqu64	zmm9,  zmmword ptr [BIN + 1*64]
	vmovdqu64	zmm10, zmmword ptr [BIN + 2*64]
	vmovdqu64	zmm11, zmmword ptr [BIN + 3*64]
	vmovdqu64	zmm12, zmmword ptr [BIN + 4*64]
	vmovdqu64	zmm13, zmmword ptr [BIN + 5*64]
	vmovdqu64	zmm14, zmmword ptr [BIN + 6*64]
	vmovdqu64	zmm15, zmmword ptr [BIN + 7*64]
	vpunpcklqdq	zmm16, zmm8, zmm9
	vpunpckhqdq	zmm17, zmm8, zmm9
	vpunpcklqdq	zmm18, zmm10, zmm11
	vpunpckhqdq	zmm19, zmm10, zmm11
	vpunpcklqdq	zmm20, zmm12, zmm13
	vpunpckhqdq	zmm21, zmm12, zmm13
	vpunpcklqdq	zmm22, zmm14, zmm15
	vpunpckhqdq	zmm23, zmm14, zmm15
	vshufi64x2	zmm8,  zmm16, zmm18, 0x88
	vshufi64x2	zmm9,  zmm16, zmm18, 0xDD
	vshufi64x2	zmm10, zmm17, zmm19, 0x88
	vshufi64x2	zmm11, zmm17, zmm19, 0xDD
	vshufi64x2	zmm12, zmm20, zmm22, 0x88
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
.LOUT_LO:	.quad 0, 1, 8, 9, 2, 3, 10, 11
.LOUT_HI:	.quad 4, 5, 12, 13, 6, 7, 14, 15

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
