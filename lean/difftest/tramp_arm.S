/* Differential-test trampoline (AArch64).  kt_in/kt_out: x0..x30 @0 (8 each), sp @248, nzcv @256,
   which @264, v0..v31 @512 (16 each).  x18 is the branch register (not part of the test). */
	.arch armv8.2-a+sha3
	.bss
	.balign 64
	.globl kt_in, kt_out
kt_in:	.skip 1024
kt_out:	.skip 1024
kt_saved_sp: .skip 8
	.text
	.globl kt_run, kt_back, kt_back2
	.type kt_run, %function
kt_run:
	stp x29, x30, [sp, #-176]!
	stp x19, x20, [sp, #16]
	stp x21, x22, [sp, #32]
	stp x23, x24, [sp, #48]
	stp x25, x26, [sp, #64]
	stp x27, x28, [sp, #80]
	stp d8, d9, [sp, #96]
	stp d10, d11, [sp, #112]
	stp d12, d13, [sp, #128]
	stp d14, d15, [sp, #144]
	str x18, [sp, #160]
	adrp x9, kt_saved_sp
	add x9, x9, :lo12:kt_saved_sp
	mov x10, sp
	str x10, [x9]
	mov x18, x0
	adrp x30, kt_in
	add x30, x30, :lo12:kt_in
	ldr x9, [x30, #248]
	mov sp, x9
	ldr x9, [x30, #256]
	msr nzcv, x9
	ldp q0, q1, [x30, #512]
	ldp q2, q3, [x30, #544]
	ldp q4, q5, [x30, #576]
	ldp q6, q7, [x30, #608]
	ldp q8, q9, [x30, #640]
	ldp q10, q11, [x30, #672]
	ldp q12, q13, [x30, #704]
	ldp q14, q15, [x30, #736]
	ldp q16, q17, [x30, #768]
	ldp q18, q19, [x30, #800]
	ldp q20, q21, [x30, #832]
	ldp q22, q23, [x30, #864]
	ldp q24, q25, [x30, #896]
	ldp q26, q27, [x30, #928]
	ldp q28, q29, [x30, #960]
	ldp q30, q31, [x30, #992]
	ldp x0, x1, [x30, #0]
	ldp x2, x3, [x30, #16]
	ldp x4, x5, [x30, #32]
	ldp x6, x7, [x30, #48]
	ldp x8, x9, [x30, #64]
	ldp x10, x11, [x30, #80]
	ldp x12, x13, [x30, #96]
	ldp x14, x15, [x30, #112]
	ldp x16, x17, [x30, #128]
	ldp x20, x21, [x30, #160]
	ldp x22, x23, [x30, #176]
	ldp x24, x25, [x30, #192]
	ldp x26, x27, [x30, #208]
	ldp x28, x29, [x30, #224]
	ldr x19, [x30, #152]
	ldr x30, [x30, #240]
	br x18
.macro SAVE which
	adrp x18, kt_out
	add x18, x18, :lo12:kt_out
	stp x0, x1, [x18, #0]
	stp x2, x3, [x18, #16]
	stp x4, x5, [x18, #32]
	stp x6, x7, [x18, #48]
	stp x8, x9, [x18, #64]
	stp x10, x11, [x18, #80]
	stp x12, x13, [x18, #96]
	stp x14, x15, [x18, #112]
	stp x16, x17, [x18, #128]
	stp x20, x21, [x18, #160]
	stp x22, x23, [x18, #176]
	stp x24, x25, [x18, #192]
	stp x26, x27, [x18, #208]
	stp x28, x29, [x18, #224]
	str x19, [x18, #152]
	str x30, [x18, #240]
	mov x0, sp
	str x0, [x18, #248]
	mrs x0, nzcv
	str x0, [x18, #256]
	mov x0, #\which
	str x0, [x18, #264]
	stp q0, q1, [x18, #512]
	stp q2, q3, [x18, #544]
	stp q4, q5, [x18, #576]
	stp q6, q7, [x18, #608]
	stp q8, q9, [x18, #640]
	stp q10, q11, [x18, #672]
	stp q12, q13, [x18, #704]
	stp q14, q15, [x18, #736]
	stp q16, q17, [x18, #768]
	stp q18, q19, [x18, #800]
	stp q20, q21, [x18, #832]
	stp q22, q23, [x18, #864]
	stp q24, q25, [x18, #896]
	stp q26, q27, [x18, #928]
	stp q28, q29, [x18, #960]
	stp q30, q31, [x18, #992]
	b kt_restore
.endm
kt_back:
	SAVE 1
kt_back2:
	SAVE 2
kt_restore:
	adrp x9, kt_saved_sp
	add x9, x9, :lo12:kt_saved_sp
	ldr x10, [x9]
	mov sp, x10
	ldp x19, x20, [sp, #16]
	ldp x21, x22, [sp, #32]
	ldp x23, x24, [sp, #48]
	ldp x25, x26, [sp, #64]
	ldp x27, x28, [sp, #80]
	ldp d8, d9, [sp, #96]
	ldp d10, d11, [sp, #112]
	ldp d12, d13, [sp, #128]
	ldp d14, d15, [sp, #144]
	ldr x18, [sp, #160]
	ldp x29, x30, [sp], #176
	ret
	.section .note.GNU-stack,"",@progbits
