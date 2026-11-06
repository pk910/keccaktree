/*
 * Function frame shared by the x86-64 batch kernels. The including file
 * defines NODES (nodes per batch), VBYTES (vector register size), a local
 * label .Lbatch that hashes NODES nodes from [BIN] to [BOUT], and
 * optionally SLOTS (bytes of kernel scratch, default two rows of lanes)
 * and the tail policy below.
 *
 * Tail policy. After the full batches, 0 < r < NODES nodes remain; which
 * code hashes them is chosen by thresholds, in this order:
 *   SMALL_TAIL_X1       a scalar kernel for r <= SMALL_TAIL_X1_MAX (default
 *                       1; a whole call of at most that many nodes goes
 *                       there before the prologue); after at least one
 *                       batch of this kernel the limit is
 *                       SMALL_TAIL_X1_MAX_AFTER instead (default
 *                       SMALL_TAIL_X1_MAX): see below why they differ.
 *   SMALL_TAIL          a smaller batch kernel for r <= SMALL_TAIL_MAX (or
 *                       the count in the quadword SMALL_TAIL_MAX_VAR, which
 *                       a kernel can expose for run-time calibration).
 *   SMALL_TAIL_MID      another kernel for r <= SMALL_TAIL_MID_MAX (or the
 *                       quadword SMALL_TAIL_MID_MAX_VAR), above SMALL_TAIL;
 *                       or, with SMALL_TAIL_MID_MASK, for the counts whose
 *                       bit is set, checked before SMALL_TAIL.
 *   otherwise           a padded batch of this kernel: the r nodes are
 *                       copied to a stack buffer, the batch hashes NODES
 *                       lanes (the rest whatever is there) and r digests
 *                       are copied out.
 * ENTRY_ALT / ENTRY_ALT2 with ENTRY_ALT_MASK / ENTRY_ALT2_MASK hand a whole
 * call to another kernel, before the prologue, when bit count of the mask
 * is set (count < 64): for the counts where that kernel, with its own
 * tail, is faster than a batch of this one plus a tail. BATCH_ALT_MASK
 * does the same for the remaining count before every batch, to
 * SMALL_TAIL_MID (avx2_x6: 9, 10 or 15 nodes left go to avx2_x5).
 *
 * Why the thresholds depend on what ran before: the kernels are chosen by
 * the time of a batch, but a kernel that follows another one may run
 * from the decoder instead of the op cache. The avx2_x10 loop body is
 * about 9 KB of dense code and fills most of the 4K-op cache of Zen 3;
 * an AVX2 kernel called after it (x2, x4, x8, x5, x9) decodes most of its
 * first batch again: +210..420 ns, measured with perf (de_src_op_disp
 * from the decoder 3665 per x4 call after x10 vs 2 when hot). The small
 * scalar kernel is not affected, and neither is a padded batch of the
 * kernel that just ran. So after an x10 batch, two nodes go to the scalar
 * kernel (440 ns, the lane-pair kernel costs 566 cold) and 5..9 nodes to
 * a padded x10 batch (683 ns; the x8 chain costs 950..1300 cold), while
 * at entry, with nothing cold, x5 (5..6 nodes) and x8 (8, 12, 16 nodes)
 * are faster than x10 batches with a tail. Cores whose op cache holds
 * both (Gracemont) hash 5..9 remaining nodes faster through x5, so that
 * limit is calibrated (keccaktree.c). The thresholds are documented with
 * the measurements in each kernel.
 *
 * Calling convention: SysV (rdi, rsi, rdx) or Windows x64 (rcx, rdx, r8),
 * where xmm6..15, rsi and rdi are callee-saved. Inside, rdi = output,
 * rsi = input, rdx = count on both, and r9 points at the 64-byte aligned
 * frame: VMEM slots first, then the tail buffers. A kernel that uses the
 * callee-saved rbx and r12..r15 defines SAVE_GPRS: the frame pushes them
 * after rbp and restores them on exit. The tail kernels are tail-called
 * after the epilogue, with the remaining nodes in the argument registers.
 */
#ifdef _WIN64
#define ARG_OUT		rcx
#define ARG_IN		rdx
#define ARG_COUNT	r8
#else
#define ARG_OUT		rdi
#define ARG_IN		rsi
#define ARG_COUNT	rdx
#endif
#define BIN		r10		/* batch input */
#define BOUT		r11		/* batch output */

#ifndef SLOTS
#define SLOTS		(10*VBYTES)		/* two rows of 5 lanes */
#endif
#define TAIL_IN		SLOTS			/* NODES x 64 bytes */
#define TAIL_OUT	(TAIL_IN + NODES*64)	/* NODES x 32 bytes */
#define SAVE		(TAIL_OUT + NODES*32)	/* Windows: xmm6..15, rsi, rdi */
#define FRAME		(SAVE + 10*16 + 16)

.macro FUNCTION name
.text
.p2align 6
.globl \name
#ifndef _WIN64
.type \name,%function
#endif
\name:
#ifdef SMALL_TAIL_X1
#ifndef SMALL_TAIL_X1_MAX
#define SMALL_TAIL_X1_MAX 1
#endif
#ifndef SMALL_TAIL_X1_MAX_AFTER
#define SMALL_TAIL_X1_MAX_AFTER SMALL_TAIL_X1_MAX
#endif
	/* a count the scalar kernel handles (0 included: it returns): no frame */
	cmp		ARG_COUNT, SMALL_TAIL_X1_MAX
	jbe		SMALL_TAIL_X1
#endif
#if defined(ENTRY_ALT) || defined(ENTRY_ALT2)
	/* counts another kernel handles faster as a whole: no frame */
	cmp		ARG_COUNT, 63
	ja		1f
#ifdef ENTRY_ALT
	mov		rax, ENTRY_ALT_MASK
	bt		rax, ARG_COUNT
	jc		ENTRY_ALT
#endif
#ifdef ENTRY_ALT2
	mov		rax, ENTRY_ALT2_MASK
	bt		rax, ARG_COUNT
	jc		ENTRY_ALT2
#endif
1:
#endif
	push		rbp
	mov		rbp, rsp
#ifdef SAVE_GPRS
	push		rbx
	push		r12
	push		r13
	push		r14
	push		r15
#endif
	/* Windows commits stack pages through a single guard page, so a frame
	 * of more than a page must touch every page on the way down (what the
	 * compiler's __chkstk does), or the first store below the guard page
	 * faults on reserved memory. One probe per page, down to the page the
	 * call to .Lbatch reaches (FRAME + 63 of alignment + 8); nothing on
	 * frames within a page. Linux grows the stack on any access, and
	 * valgrind reports an access below rsp, so SysV probes only when a
	 * test asks for it (KECCAKTREE_STACK_PROBE: the guard-page emulation
	 * test exercises the Windows rule on Linux). */
#if defined(_WIN64) || defined(KECCAKTREE_STACK_PROBE)
.set .Lprobe, 4096
.rept (FRAME + 72) / 4096
	or		qword ptr [rsp - .Lprobe], 0
.set .Lprobe, .Lprobe + 4096
.endr
#endif
	sub		rsp, FRAME
	and		rsp, -64
#ifdef _WIN64
	vmovdqu		xmmword ptr [rsp + SAVE + 0*16], xmm6
	vmovdqu		xmmword ptr [rsp + SAVE + 1*16], xmm7
	vmovdqu		xmmword ptr [rsp + SAVE + 2*16], xmm8
	vmovdqu		xmmword ptr [rsp + SAVE + 3*16], xmm9
	vmovdqu		xmmword ptr [rsp + SAVE + 4*16], xmm10
	vmovdqu		xmmword ptr [rsp + SAVE + 5*16], xmm11
	vmovdqu		xmmword ptr [rsp + SAVE + 6*16], xmm12
	vmovdqu		xmmword ptr [rsp + SAVE + 7*16], xmm13
	vmovdqu		xmmword ptr [rsp + SAVE + 8*16], xmm14
	vmovdqu		xmmword ptr [rsp + SAVE + 9*16], xmm15
	mov		qword ptr [rsp + SAVE + 10*16], rsi
	mov		qword ptr [rsp + SAVE + 10*16 + 8], rdi
	mov		rdi, ARG_OUT
	mov		rsi, ARG_IN
	mov		rdx, ARG_COUNT
#endif
	mov		r9, rsp
	mov		BIN, rsi
	mov		BOUT, rdi
1:	cmp		rdx, NODES
	jb		2f
9:	/* full batches */
#ifdef BATCH_ALT_MASK
	/* counts (< 64) that SMALL_TAIL_MID hashes faster than a batch here
	 * and the tail of the rest, checked before every batch */
	cmp		rdx, 63
	ja		10f
	mov		rax, BATCH_ALT_MASK
	bt		rax, rdx
	jnc		10f
	mov		eax, 3
	jmp		5f
10:
#endif
	call		.Lbatch
	add		BIN, NODES*64
	add		BOUT, NODES*32
	sub		rdx, NODES
	cmp		rdx, NODES
	jae		9b
#ifdef SMALL_TAIL_X1
	/* 0 <= rdx < NODES after a batch of this kernel */
	cmp		rdx, SMALL_TAIL_X1_MAX_AFTER
	ja		2f
	test		rdx, rdx
	jz		4f
	mov		eax, 2
	jmp		5f
#endif
2:	/* 0 <= rdx < NODES, and above SMALL_TAIL_X1_MAX unless a batch ran */
	test		rdx, rdx
	jz		4f
#ifdef SMALL_TAIL_MID_MASK
	mov		eax, SMALL_TAIL_MID_MASK
	bt		rax, rdx
	jnc		3f
	mov		eax, 3
	jmp		5f
3:
#endif
#ifdef SMALL_TAIL
#ifdef SMALL_TAIL_MAX_VAR
	cmp		rdx, qword ptr [rip + SMALL_TAIL_MAX_VAR]
#else
	cmp		rdx, SMALL_TAIL_MAX
#endif
	ja		3f
	mov		eax, 1
	jmp		5f
3:
#endif
#if defined(SMALL_TAIL_MID) && !defined(SMALL_TAIL_MID_MASK)
#ifdef SMALL_TAIL_MID_MAX_VAR
	cmp		rdx, qword ptr [rip + SMALL_TAIL_MID_MAX_VAR]
#else
	cmp		rdx, SMALL_TAIL_MID_MAX
#endif
	ja		3f
	mov		eax, 3
	jmp		5f
3:
#endif
	/* hash a copy in the stack buffer; lanes past count hash whatever is
	 * there and are not stored. The copies are vector loops, not rep movsb:
	 * at these sizes (64..640 bytes) rep movsb's startup costs more than
	 * the copy itself (Zen 3: ~20 ns per tail with rep movsb, ~5 with
	 * ymm moves). */
	mov		rax, rdx
	mov		rsi, BIN
	lea		rdi, [rsp + TAIL_IN]
	mov		rcx, rax
7:	vmovdqu		ymm0, ymmword ptr [rsi]
	vmovdqu		ymm1, ymmword ptr [rsi + 32]
	vmovdqu		ymmword ptr [rdi], ymm0
	vmovdqu		ymmword ptr [rdi + 32], ymm1
	add		rsi, 64
	add		rdi, 64
	dec		rcx
	jnz		7b
	mov		rdi, BOUT
	lea		BIN, [rsp + TAIL_IN]
	lea		BOUT, [rsp + TAIL_OUT]
	call		.Lbatch
	lea		rsi, [rsp + TAIL_OUT]
	mov		rcx, rax
8:	vmovdqu		ymm0, ymmword ptr [rsi]
	vmovdqu		ymmword ptr [rdi], ymm0
	add		rsi, 32
	add		rdi, 32
	dec		rcx
	jnz		8b
4:	/* done */
	xor		eax, eax
5:	/* eax != 0: tail-call SMALL_TAIL (1), SMALL_TAIL_X1 (2) or
	 * SMALL_TAIL_MID (3) for the rest (rdx nodes at BIN -> BOUT) */
	vzeroupper
#ifdef _WIN64
	vmovdqu		xmm6,  xmmword ptr [rsp + SAVE + 0*16]
	vmovdqu		xmm7,  xmmword ptr [rsp + SAVE + 1*16]
	vmovdqu		xmm8,  xmmword ptr [rsp + SAVE + 2*16]
	vmovdqu		xmm9,  xmmword ptr [rsp + SAVE + 3*16]
	vmovdqu		xmm10, xmmword ptr [rsp + SAVE + 4*16]
	vmovdqu		xmm11, xmmword ptr [rsp + SAVE + 5*16]
	vmovdqu		xmm12, xmmword ptr [rsp + SAVE + 6*16]
	vmovdqu		xmm13, xmmword ptr [rsp + SAVE + 7*16]
	vmovdqu		xmm14, xmmword ptr [rsp + SAVE + 8*16]
	vmovdqu		xmm15, xmmword ptr [rsp + SAVE + 9*16]
	mov		rsi, qword ptr [rsp + SAVE + 10*16]
	mov		rdi, qword ptr [rsp + SAVE + 10*16 + 8]
#endif
#ifdef SAVE_GPRS
	lea		rsp, [rbp - 40]
	pop		r15
	pop		r14
	pop		r13
	pop		r12
	pop		rbx
#else
	mov		rsp, rbp
#endif
	pop		rbp
#if defined(SMALL_TAIL) || defined(SMALL_TAIL_X1) || defined(SMALL_TAIL_MID)
	test		eax, eax
	jz		6f
	mov		ARG_COUNT, rdx
	mov		ARG_OUT, BOUT
	mov		ARG_IN, BIN
#ifdef SMALL_TAIL_X1
	cmp		eax, 2
	je		SMALL_TAIL_X1
#endif
#ifdef SMALL_TAIL_MID
	cmp		eax, 3
	je		SMALL_TAIL_MID
#endif
#ifdef SMALL_TAIL
	jmp		SMALL_TAIL
#endif
6:
#endif
	ret
#ifndef _WIN64
.size \name, .-\name
#endif
.endm

/* constants shared by the kernels */
.macro KECCAK_RODATA
#ifdef _WIN64
.section .rdata,"dr"
#else
.section .rodata
#endif
.p2align 6
.LKECCAK_RC:
	.quad 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000
	.quad 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009
	.quad 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a
	.quad 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003
	.quad 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a
	.quad 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
.LK1:	.quad 0x0000000000000001
.LK63:	.quad 0x8000000000000000
.endm
