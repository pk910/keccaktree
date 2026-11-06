/*
 * void keccaktree_keccak256_avx2_x5(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 5 at a time: the
 * 4-node batch of keccak256_avx2_x4 in the vector registers plus one node
 * in the general registers (keccak256_x86_scalar.inc), its round spread
 * through the vector round as in keccak256_avx2_x9.S. Needs AVX2, BMI1
 * and BMI2. A single remaining node goes to keccaktree_keccak256_x86_x1,
 * 2..4 to keccaktree_keccak256_avx2_x4.
 *
 * Registers: ymm0..15, rsi and the frame's r9..r11 for the vector stream;
 * rax, rbx, rcx, rdx, rdi, rbp, r8, r12..r15 for the scalar node.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#define NODES		5
#define VBYTES		32
#define SLOTS		(50*32 + 448 + 64 + 48 + 80)
#define SMALL_TAIL_X1	keccaktree_keccak256_x86_x1	/* a single node: scalar directly */
#define SMALL_TAIL	keccaktree_keccak256_avx2_x4	/* 2..4 nodes */
#define SMALL_TAIL_MAX	4
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
#define SPAR_MEM	0
/* 65 scalar chunks over the 55 hooks of a vector round */
#ifndef SNUM
#define SNUM		6
#define SDEN		5
#endif
#include "keccak256_x86_scalar.inc"
#include "keccak256_avx2.inc"

/* frame layout at r9 (= rsp): the two vector state buffers, the two
 * scalar state buffers, the scalar digest and the saved registers */
#define BUF0		r9
#define BUF1		r9+25*32
#define SS0		(50*32)
#define SS1		(50*32 + 224)
#define SOUT		(50*32 + 448)
#define SAVE_RAX	(SOUT + 64)
#define SAVE_RDX	(SOUT + 72)
#define SAVE_RDI	(SOUT + 80)
#define SAVE_RBP	(SOUT + 88)
#define SCNT		(SOUT + 96)

.text
.p2align 6
/* one batch: 5 nodes at [BIN] -> 5 digests at [BOUT] */
.Lbatch:
	mov		qword ptr [r9 + SAVE_RAX], rax
	mov		qword ptr [r9 + SAVE_RDX], rdx
	mov		qword ptr [r9 + SAVE_RDI], rdi
	mov		qword ptr [r9 + SAVE_RBP], rbp
	lea		RCP, [rip + .LRC4]
	vmovdqu		ymm0, ymmword ptr [BIN + 4*64]
	vmovdqu		ymm1, ymmword ptr [BIN + 4*64 + 32]
	vmovdqa		ymmword ptr [r9 + SS0], ymm0
	vmovdqa		ymmword ptr [r9 + SS0 + 32], ymm1

	SROUND_BEGIN	0, SS0, SS1, 0, 0
	LOAD		BIN
	ROUND0		BUF1, BUF0
	SFLUSH

	/* rounds 1..22, two per iteration */
	mov		qword ptr [r9 + SCNT], 11
1:
	SROUND_BEGIN	1, SS1, SS0, 32, 1
	ROUND		BUF0, BUF1, 32
	SFLUSH
	SROUND_BEGIN	1, SS0, SS1, 64, 0
	ROUND		BUF1, BUF0, 64
	SFLUSH
	add		RCP, 64
	dec		qword ptr [r9 + SCNT]
	jnz		1b

	SROUND_BEGIN	23, SS1, SOUT, 32, 1
	ROUND23		BUF0, 32
	OUTPUT		BOUT
	SFLUSH
	vmovdqu		ymm0, ymmword ptr [r9 + SOUT]
	vmovdqu		ymmword ptr [BOUT + 4*32], ymm0
	mov		rax, qword ptr [r9 + SAVE_RAX]
	mov		rdx, qword ptr [r9 + SAVE_RDX]
	mov		rdi, qword ptr [r9 + SAVE_RDI]
	mov		rbp, qword ptr [r9 + SAVE_RBP]
	ret

	FUNCTION keccaktree_keccak256_avx2_x5
	AVX2_RODATA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
