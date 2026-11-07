/* Differential-test trampoline (x86-64): load a full register state, jump to a
   test snippet, capture the state when the snippet jumps to kt_back/kt_back2.
   Layout of kt_in/kt_out: gpr[16] @0, rflags @128, which @136, vec[32][64B] @256, k[8] (16 bit, 8B slots) @2304. */
.intel_syntax noprefix
.bss
.balign 64
.globl kt_in, kt_out
kt_in:  .skip 2432
kt_out: .skip 2432
kt_saved_rsp: .skip 8
kt_target: .skip 8
.text
.globl kt_run, kt_back, kt_back2
kt_run:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	mov [rip+kt_saved_rsp], rsp
	mov [rip+kt_target], rdi
#ifdef AVX512
	.irp i,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
	vmovdqu64 zmm\i, [rip+kt_in+256+64*\i]
	.endr
	.irp i,0,1,2,3,4,5,6,7
	kmovw k\i, [rip+kt_in+2304+8*\i]
	.endr
#else
	.irp i,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	vmovdqu ymm\i, [rip+kt_in+256+64*\i]
	.endr
#endif
	lea rsp, [rip+kt_in+128]
	popfq
	mov rax, [rip+kt_in+0]
	mov rcx, [rip+kt_in+8]
	mov rdx, [rip+kt_in+16]
	mov rbx, [rip+kt_in+24]
	mov rsp, [rip+kt_in+32]
	mov rbp, [rip+kt_in+40]
	mov rsi, [rip+kt_in+48]
	mov rdi, [rip+kt_in+56]
	mov r8, [rip+kt_in+64]
	mov r9, [rip+kt_in+72]
	mov r10, [rip+kt_in+80]
	mov r11, [rip+kt_in+88]
	mov r12, [rip+kt_in+96]
	mov r13, [rip+kt_in+104]
	mov r14, [rip+kt_in+112]
	mov r15, [rip+kt_in+120]
	jmp [rip+kt_target]
kt_back:
	mov qword ptr [rip+kt_out+136], 1
	jmp kt_save
kt_back2:
	mov qword ptr [rip+kt_out+136], 2
kt_save:
	mov [rip+kt_out+0], rax
	mov [rip+kt_out+8], rcx
	mov [rip+kt_out+16], rdx
	mov [rip+kt_out+24], rbx
	mov [rip+kt_out+32], rsp
	mov [rip+kt_out+40], rbp
	mov [rip+kt_out+48], rsi
	mov [rip+kt_out+56], rdi
	mov [rip+kt_out+64], r8
	mov [rip+kt_out+72], r9
	mov [rip+kt_out+80], r10
	mov [rip+kt_out+88], r11
	mov [rip+kt_out+96], r12
	mov [rip+kt_out+104], r13
	mov [rip+kt_out+112], r14
	mov [rip+kt_out+120], r15
	lea rsp, [rip+kt_out+136]
	pushfq
#ifdef AVX512
	.irp i,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
	vmovdqu64 [rip+kt_out+256+64*\i], zmm\i
	.endr
	.irp i,0,1,2,3,4,5,6,7
	kmovw [rip+kt_out+2304+8*\i], k\i
	.endr
#else
	.irp i,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	vmovdqu [rip+kt_out+256+64*\i], ymm\i
	.endr
#endif
	vzeroupper
	mov rsp, [rip+kt_saved_rsp]
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
.section .note.GNU-stack,"",@progbits
