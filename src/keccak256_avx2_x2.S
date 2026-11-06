/*
 * void keccaktree_keccak256_avx2_x2(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 2 at a time with
 * the lane-pair rounds of keccak256_avx2_pair.inc: for 2 nodes a padded
 * 4-node batch of keccak256_avx2_x4 does the vector work of 4 nodes, this
 * does about 80% of it; a single node goes to the scalar code. Meant as
 * the remainder path of the 4- and 8-node kernels (counts 2, 6).
 *
 * Registers: ymm0..15; rcx, rsi here and the frame's r9..r11.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#define NODES		2
#define VBYTES		32
#define SLOTS		(30*32)			/* the two state buffers */
#define SMALL_TAIL	keccaktree_keccak256_x86_x1
#define SMALL_TAIL_MAX	1
#include "keccak256_x86_frame.inc"

#define RCP		rsi			/* round constants */
#include "keccak256_avx2_pair.inc"

/* the two state buffers at r9 (= rsp); no spaces: macro arguments */
#define SA		r9
#define SB		r9+15*32

.text
.p2align 6
/* one batch: 2 nodes at [BIN] -> 2 digests at [BOUT] */
.Lbatch:
	LOAD		BIN, SA
	lea		RCP, [rip + .LRC2]
	mov		ecx, 12
1:
	ROUND		SA, SB, 0
	ROUND		SB, SA, 32
	add		RCP, 64
	dec		ecx
	jnz		1b
	OUTPUT		SA, BOUT
	ret

	FUNCTION keccaktree_keccak256_avx2_x2
	PAIR_RODATA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
