/*
 * void keccaktree_keccak256_avx2_hybrid(unsigned char *output,
 *                                       const unsigned char *input, uint64_t count)
 *
 * Per-core dispatch for x86-64 CPUs with more than one kind of core (the
 * CPUID hybrid flag: Intel Alder Lake and later). The fastest AVX2 kernel
 * differs by core: avx2_x8 on the P-cores, whose integer ALUs share ports
 * with the vector units, avx2_x6 on the E-cores, where two scalar nodes
 * ride along the 4-node batch. Running the other core's kernel costs 32%
 * (avx2_x8 on Gracemont) to 54% (avx2_x6 on Raptor Cove) at 1024 nodes,
 * and the scheduler moves threads between the two at will, so the choice
 * is made on every call from the core the call is on:
 *
 *   rdpid            IA32_TSC_AUX, which Linux and Windows set to the
 *                    logical CPU number (a few cycles, no exit under a
 *                    hypervisor)
 *   .Lcore[aux & 255] 0 = not seen yet, 1 = P-core, 2 = E-core
 *
 * The first call on a logical CPU reads its core type from CPUID leaf 1AH
 * (EAX[31:24]: 20H Atom, 40H Core; about 100 cycles, once per CPU) and
 * stores it, unless the thread was moved between the two reads. Nothing
 * here is timed. A thread that migrates after the lookup runs one call
 * with the other core's kernel, which is only slower: both kernels run on
 * both cores. An OS that leaves IA32_TSC_AUX at one value for all CPUs
 * degrades to the kernel of the first core seen.
 *
 * Needs RDPID besides AVX2, BMI1 and BMI2 (every hybrid CPU has it);
 * keccaktree_detect returns this kernel only when CPUID reports both.
 * No stack frame beyond three pushes on the first call per CPU; the
 * kernels are tail-called with the arguments untouched.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#if defined(__CET__) && defined(__ELF__)
#include <cet.h>			/* IBT / shadow stack note, endbr64 */
#else
#define _CET_ENDBR
#endif

.macro RDPID_RAX
	.byte		0xf3, 0x0f, 0xc7, 0xf8	/* rdpid rax (binutils 2.28+) */
.endm

.text
.p2align 6
.globl keccaktree_keccak256_avx2_hybrid
#ifndef _WIN64
.type keccaktree_keccak256_avx2_hybrid,%function
#endif
keccaktree_keccak256_avx2_hybrid:
	_CET_ENDBR
	RDPID_RAX
	movzx		eax, al
	lea		r9, [rip + .Lcore]
	movzx		r10d, byte ptr [r9 + rax]
	cmp		r10d, 1
	je		keccaktree_keccak256_avx2_x8
	ja		keccaktree_keccak256_avx2_x6
	/* first call on this logical CPU: cpuid clobbers rax, rbx, rcx, rdx
	 * (rbx is callee-saved, rcx and rdx carry arguments) */
	push		rbx
	push		rcx
	push		rdx
	mov		r11d, eax
	mov		eax, 0x1a
	xor		ecx, ecx
	cpuid
	shr		eax, 24
	xor		r10d, r10d
	cmp		eax, 0x20
	sete		r10b
	inc		r10d			/* 1 = P-core, 2 = E-core */
	RDPID_RAX
	movzx		eax, al
	cmp		eax, r11d
	jne		1f			/* moved meanwhile: do not record */
	mov		byte ptr [r9 + r11], r10b
1:	pop		rdx
	pop		rcx
	pop		rbx
	cmp		r10d, 1
	je		keccaktree_keccak256_avx2_x8
	jmp		keccaktree_keccak256_avx2_x6
#ifndef _WIN64
.size keccaktree_keccak256_avx2_hybrid, .-keccaktree_keccak256_avx2_hybrid
#endif

.bss
.p2align 6
.Lcore:
	.zero		256

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
