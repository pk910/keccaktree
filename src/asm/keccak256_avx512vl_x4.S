/*
 * void keccaktree_keccak256_avx512vl_x4(unsigned char *output,
 *                                       const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 4 at a time: node j
 * of a batch lives in qword lane j of every ymm register. AVX-512F + VL
 * (vprolq, vpternlogq and ymm16..31 on 256-bit vectors). Same rounds as the
 * zmm kernel (keccak256_avx512.inc). Used on Intel client cores, whose
 * 512-bit ALU is a single port, and for the last 1..4 nodes of the zmm one.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#define NODES		4
#define VBYTES		32
#define VR		ymm
#define VREG(n)		VREG_(n)
#define VREG_(n)	ymm##n
#define VMEM(i)		ymmword ptr [r9 + 32*(i)]
#define RC(r)		qword ptr [rip + .LKECCAK_RC + 8*(r)]{1to4}
#define K1		qword ptr [rip + .LK1]{1to4}
#define K63		qword ptr [rip + .LK63]{1to4}

#include "keccak256_x86_frame.inc"
#include "keccak256_avx512.inc"

/* digest words o0..o3 (4 nodes each) -> 4 x 32 bytes at [BOUT] */
.macro OUTPUT o0, o1, o2, o3
	vpunpcklqdq	ymm25, VR\o0, VR\o1		/* n0, n2: w0 w1 */
	vpunpckhqdq	ymm26, VR\o0, VR\o1		/* n1, n3: w0 w1 */
	vpunpcklqdq	ymm27, VR\o2, VR\o3		/* n0, n2: w2 w3 */
	vpunpckhqdq	ymm28, VR\o2, VR\o3		/* n1, n3: w2 w3 */
	vshufi64x2	ymm0, ymm25, ymm27, 0x0	/* node 0 */
	vshufi64x2	ymm1, ymm26, ymm28, 0x0	/* node 1 */
	vshufi64x2	ymm2, ymm25, ymm27, 0x3	/* node 2 */
	vshufi64x2	ymm3, ymm26, ymm28, 0x3	/* node 3 */
	vmovdqu64	ymmword ptr [BOUT + 0*32], ymm0
	vmovdqu64	ymmword ptr [BOUT + 1*32], ymm1
	vmovdqu64	ymmword ptr [BOUT + 2*32], ymm2
	vmovdqu64	ymmword ptr [BOUT + 3*32], ymm3
.endm

.text
.p2align 6
/* one batch: 4 nodes at [BIN] -> 4 digests at [BOUT] */
.Lbatch:
	/* two 4x4 qword transposes: VREG(j) = word j of nodes 0..3 */
	vmovdqu64	ymm16, ymmword ptr [BIN + 0*64]
	vmovdqu64	ymm17, ymmword ptr [BIN + 1*64]
	vmovdqu64	ymm18, ymmword ptr [BIN + 2*64]
	vmovdqu64	ymm19, ymmword ptr [BIN + 3*64]
	vmovdqu64	ymm20, ymmword ptr [BIN + 0*64 + 32]
	vmovdqu64	ymm21, ymmword ptr [BIN + 1*64 + 32]
	vmovdqu64	ymm22, ymmword ptr [BIN + 2*64 + 32]
	vmovdqu64	ymm23, ymmword ptr [BIN + 3*64 + 32]
	vpunpcklqdq	ymm24, ymm16, ymm17
	vpunpckhqdq	ymm25, ymm16, ymm17
	vpunpcklqdq	ymm26, ymm18, ymm19
	vpunpckhqdq	ymm27, ymm18, ymm19
	vshufi64x2	ymm0, ymm24, ymm26, 0x0
	vshufi64x2	ymm2, ymm24, ymm26, 0x3
	vshufi64x2	ymm1, ymm25, ymm27, 0x0
	vshufi64x2	ymm3, ymm25, ymm27, 0x3
	vpunpcklqdq	ymm24, ymm20, ymm21
	vpunpckhqdq	ymm25, ymm20, ymm21
	vpunpcklqdq	ymm26, ymm22, ymm23
	vpunpckhqdq	ymm27, ymm22, ymm23
	vshufi64x2	ymm4, ymm24, ymm26, 0x0
	vshufi64x2	ymm6, ymm24, ymm26, 0x3
	vshufi64x2	ymm5, ymm25, ymm27, 0x0
	vshufi64x2	ymm7, ymm25, ymm27, 0x3
	KECCAK_F
	ret

	FUNCTION keccaktree_keccak256_avx512vl_x4

	KECCAK_RODATA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
