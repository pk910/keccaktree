/*
 * void keccaktree_keccak256_avx2_x4(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 4 at a time with
 * the rounds of keccak256_avx2.inc; rounds 1..22 are a plain loop between
 * the two state buffers, with the row-pipelined ROUNDP (the rho of each
 * row starts inside the chi of the row before; +2% on Zen 3 over ROUND).
 * A single node goes to the scalar code, which is faster than a padded
 * batch everywhere; two nodes go to the lane-pair kernel when
 * keccaktree_avx2_small_tail(2) has enabled it (the detection times it
 * against a padded batch: it wins on Zen 3 and Gracemont, loses on Golden
 * Cove), three are padded. keccak256_avx2_x8 is faster for 8 or more
 * nodes and tail-calls this kernel for its remainder.
 *
 * Registers: ymm0..15; rcx, rsi, r8 here and the frame's r9..r11.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#define NODES		4
#define VBYTES		32
#define SLOTS		(50*32)			/* the two state buffers */
#define SMALL_TAIL_X1	keccaktree_keccak256_x86_x1	/* a single node: scalar is faster */
#define SMALL_TAIL	keccaktree_keccak256_avx2_x2	/* 2 nodes: lane pairs, where enabled */
#define SMALL_TAIL_MAX_VAR	.Lsmall_tail_max
#include "keccak256_x86_frame.inc"

#define RCP		rsi			/* round constants (broadcast) */
#include "keccak256_avx2.inc"

#define BUF0		r9			/* = rsp, state buffer 0 */
#define BUF1		r8			/* state buffer 1 */

.text
.p2align 6
/* one batch: 4 nodes at [BIN] -> 4 digests at [BOUT] */
.Lbatch:
	LOAD		BIN
	lea		BUF1, [BUF0 + 25*32]
	lea		RCP, [rip + .LRC4]
	ROUND0		BUF1, BUF0

	/* rounds 1..22, two per iteration */
	mov		ecx, 11
1:
	ROUNDP		BUF0, BUF1, 32
	ROUNDP		BUF1, BUF0, 64
	add		RCP, 64
	dec		ecx
	jnz		1b

	ROUND23		BUF0, 32
	OUTPUT		BOUT
	ret

	FUNCTION keccaktree_keccak256_avx2_x4
	AVX2_RODATA

/* void keccaktree_avx2_small_tail(uint64_t max): 2..max remaining nodes go
 * to keccaktree_keccak256_avx2_x2 (max = 2) or a padded batch (max = 1) */
.data
.p2align 3
.Lsmall_tail_max:
	.quad 1
.text
.p2align 4
.globl keccaktree_avx2_small_tail
#ifndef _WIN64
.type keccaktree_avx2_small_tail,%function
#endif
keccaktree_avx2_small_tail:
	mov		qword ptr [rip + .Lsmall_tail_max], ARG_OUT
	ret
#ifndef _WIN64
.size keccaktree_avx2_small_tail, .-keccaktree_avx2_small_tail
#endif

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
