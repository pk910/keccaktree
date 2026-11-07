/* Differential-test trampoline (RISC-V).  kt_in/kt_out: x0..x31 @8*i, vl @264, which @272, target @280,
   v0..v31 @512 (64 bytes each, VLEN <= 512).  ra returns to kt_back; gp is the base/branch register;
   gp/tp are not part of the test. */
	.option norvc
	.option norelax
	.attribute arch, "rv64gcv_zbb_zvkb"
	.bss
	.balign 64
	.globl kt_in, kt_out
kt_in:	.skip 2560
kt_out:	.skip 2560
kt_save:	.skip 256
	.text
	.globl kt_run, kt_back
	.type kt_run, @function
kt_run:
	la t0, kt_save
	sd x1, 0(t0)
	sd x2, 8(t0)
	sd x3, 16(t0)
	sd x4, 24(t0)
	sd x8, 32(t0)
	sd x9, 40(t0)
	sd x18, 48(t0)
	sd x19, 56(t0)
	sd x20, 64(t0)
	sd x21, 72(t0)
	sd x22, 80(t0)
	sd x23, 88(t0)
	sd x24, 96(t0)
	sd x25, 104(t0)
	sd x26, 112(t0)
	sd x27, 120(t0)
	la gp, kt_in
	sd a0, 280(gp)
	vsetvli t0, zero, e64, m1, ta, ma
	li t1, 512
	add t1, t1, gp
	vle64.v v0, (t1)
	li t1, 576
	add t1, t1, gp
	vle64.v v1, (t1)
	li t1, 640
	add t1, t1, gp
	vle64.v v2, (t1)
	li t1, 704
	add t1, t1, gp
	vle64.v v3, (t1)
	li t1, 768
	add t1, t1, gp
	vle64.v v4, (t1)
	li t1, 832
	add t1, t1, gp
	vle64.v v5, (t1)
	li t1, 896
	add t1, t1, gp
	vle64.v v6, (t1)
	li t1, 960
	add t1, t1, gp
	vle64.v v7, (t1)
	li t1, 1024
	add t1, t1, gp
	vle64.v v8, (t1)
	li t1, 1088
	add t1, t1, gp
	vle64.v v9, (t1)
	li t1, 1152
	add t1, t1, gp
	vle64.v v10, (t1)
	li t1, 1216
	add t1, t1, gp
	vle64.v v11, (t1)
	li t1, 1280
	add t1, t1, gp
	vle64.v v12, (t1)
	li t1, 1344
	add t1, t1, gp
	vle64.v v13, (t1)
	li t1, 1408
	add t1, t1, gp
	vle64.v v14, (t1)
	li t1, 1472
	add t1, t1, gp
	vle64.v v15, (t1)
	li t1, 1536
	add t1, t1, gp
	vle64.v v16, (t1)
	li t1, 1600
	add t1, t1, gp
	vle64.v v17, (t1)
	li t1, 1664
	add t1, t1, gp
	vle64.v v18, (t1)
	li t1, 1728
	add t1, t1, gp
	vle64.v v19, (t1)
	li t1, 1792
	add t1, t1, gp
	vle64.v v20, (t1)
	li t1, 1856
	add t1, t1, gp
	vle64.v v21, (t1)
	li t1, 1920
	add t1, t1, gp
	vle64.v v22, (t1)
	li t1, 1984
	add t1, t1, gp
	vle64.v v23, (t1)
	li t1, 2048
	add t1, t1, gp
	vle64.v v24, (t1)
	li t1, 2112
	add t1, t1, gp
	vle64.v v25, (t1)
	li t1, 2176
	add t1, t1, gp
	vle64.v v26, (t1)
	li t1, 2240
	add t1, t1, gp
	vle64.v v27, (t1)
	li t1, 2304
	add t1, t1, gp
	vle64.v v28, (t1)
	li t1, 2368
	add t1, t1, gp
	vle64.v v29, (t1)
	li t1, 2432
	add t1, t1, gp
	vle64.v v30, (t1)
	li t1, 2496
	add t1, t1, gp
	vle64.v v31, (t1)
	ld t0, 264(gp)
	vsetvli zero, t0, e64, m1, ta, ma
	ld x2, 16(gp)
	ld x5, 40(gp)
	ld x6, 48(gp)
	ld x7, 56(gp)
	ld x8, 64(gp)
	ld x9, 72(gp)
	ld x10, 80(gp)
	ld x11, 88(gp)
	ld x12, 96(gp)
	ld x13, 104(gp)
	ld x14, 112(gp)
	ld x15, 120(gp)
	ld x16, 128(gp)
	ld x17, 136(gp)
	ld x18, 144(gp)
	ld x19, 152(gp)
	ld x20, 160(gp)
	ld x21, 168(gp)
	ld x22, 176(gp)
	ld x23, 184(gp)
	ld x24, 192(gp)
	ld x25, 200(gp)
	ld x26, 208(gp)
	ld x27, 216(gp)
	ld x28, 224(gp)
	ld x29, 232(gp)
	ld x30, 240(gp)
	ld x31, 248(gp)
	la ra, kt_back
	ld gp, 280(gp)
	jr gp
kt_back:
	la gp, kt_out
	sd x1, 8(gp)
	sd x2, 16(gp)
	sd x5, 40(gp)
	sd x6, 48(gp)
	sd x7, 56(gp)
	sd x8, 64(gp)
	sd x9, 72(gp)
	sd x10, 80(gp)
	sd x11, 88(gp)
	sd x12, 96(gp)
	sd x13, 104(gp)
	sd x14, 112(gp)
	sd x15, 120(gp)
	sd x16, 128(gp)
	sd x17, 136(gp)
	sd x18, 144(gp)
	sd x19, 152(gp)
	sd x20, 160(gp)
	sd x21, 168(gp)
	sd x22, 176(gp)
	sd x23, 184(gp)
	sd x24, 192(gp)
	sd x25, 200(gp)
	sd x26, 208(gp)
	sd x27, 216(gp)
	sd x28, 224(gp)
	sd x29, 232(gp)
	sd x30, 240(gp)
	sd x31, 248(gp)
	csrr t0, vl
	sd t0, 264(gp)
	li t0, 1
	sd t0, 272(gp)
	vsetvli t0, zero, e64, m1, ta, ma
	li t1, 512
	add t1, t1, gp
	vse64.v v0, (t1)
	li t1, 576
	add t1, t1, gp
	vse64.v v1, (t1)
	li t1, 640
	add t1, t1, gp
	vse64.v v2, (t1)
	li t1, 704
	add t1, t1, gp
	vse64.v v3, (t1)
	li t1, 768
	add t1, t1, gp
	vse64.v v4, (t1)
	li t1, 832
	add t1, t1, gp
	vse64.v v5, (t1)
	li t1, 896
	add t1, t1, gp
	vse64.v v6, (t1)
	li t1, 960
	add t1, t1, gp
	vse64.v v7, (t1)
	li t1, 1024
	add t1, t1, gp
	vse64.v v8, (t1)
	li t1, 1088
	add t1, t1, gp
	vse64.v v9, (t1)
	li t1, 1152
	add t1, t1, gp
	vse64.v v10, (t1)
	li t1, 1216
	add t1, t1, gp
	vse64.v v11, (t1)
	li t1, 1280
	add t1, t1, gp
	vse64.v v12, (t1)
	li t1, 1344
	add t1, t1, gp
	vse64.v v13, (t1)
	li t1, 1408
	add t1, t1, gp
	vse64.v v14, (t1)
	li t1, 1472
	add t1, t1, gp
	vse64.v v15, (t1)
	li t1, 1536
	add t1, t1, gp
	vse64.v v16, (t1)
	li t1, 1600
	add t1, t1, gp
	vse64.v v17, (t1)
	li t1, 1664
	add t1, t1, gp
	vse64.v v18, (t1)
	li t1, 1728
	add t1, t1, gp
	vse64.v v19, (t1)
	li t1, 1792
	add t1, t1, gp
	vse64.v v20, (t1)
	li t1, 1856
	add t1, t1, gp
	vse64.v v21, (t1)
	li t1, 1920
	add t1, t1, gp
	vse64.v v22, (t1)
	li t1, 1984
	add t1, t1, gp
	vse64.v v23, (t1)
	li t1, 2048
	add t1, t1, gp
	vse64.v v24, (t1)
	li t1, 2112
	add t1, t1, gp
	vse64.v v25, (t1)
	li t1, 2176
	add t1, t1, gp
	vse64.v v26, (t1)
	li t1, 2240
	add t1, t1, gp
	vse64.v v27, (t1)
	li t1, 2304
	add t1, t1, gp
	vse64.v v28, (t1)
	li t1, 2368
	add t1, t1, gp
	vse64.v v29, (t1)
	li t1, 2432
	add t1, t1, gp
	vse64.v v30, (t1)
	li t1, 2496
	add t1, t1, gp
	vse64.v v31, (t1)
	la t0, kt_save
	ld x1, 0(t0)
	ld x2, 8(t0)
	ld x3, 16(t0)
	ld x4, 24(t0)
	ld x8, 32(t0)
	ld x9, 40(t0)
	ld x18, 48(t0)
	ld x19, 56(t0)
	ld x20, 64(t0)
	ld x21, 72(t0)
	ld x22, 80(t0)
	ld x23, 88(t0)
	ld x24, 96(t0)
	ld x25, 104(t0)
	ld x26, 112(t0)
	ld x27, 120(t0)
	ret
	.section .note.GNU-stack,"",@progbits
