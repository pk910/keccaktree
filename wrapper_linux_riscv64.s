//go:build cgo && linux && riscv64

// The C kernels run on this frame's 2048 bytes of stack (deepest: the
// vector kernels' 512-byte bounce buffer). SP is moved to the top of the
// frame and 16-byte aligned as the C ABI wants; X9 (s1, callee-saved in C)
// keeps the Go SP. Selection: rvKernel, see bindings_linux_riscv64.go.
TEXT ·KeccaktreeHash(SB), 0, $2048-24
	MOV   output+0(FP), X10
	MOV   input+8(FP), X11
	MOV   count+16(FP), X12
	MOVBU ·rvKernel(SB), X5

	MOV   X2, X9
	ADD   $2048, X2
	AND   $~15, X2

	MOV   $3, X6
	BEQ   X5, X6, zvkb
	MOV   $2, X6
	BEQ   X5, X6, rvv
	BNEZ  X5, zbb
	CALL  keccaktree_keccak256_rv64_x1(SB)
	JMP   epilog

zbb:
	CALL  keccaktree_keccak256_zbb_x1(SB)
	JMP   epilog

rvv:
	CALL  keccaktree_keccak256_rvv(SB)
	JMP   epilog

zvkb:
	CALL  keccaktree_keccak256_rvv_zvkb(SB)

epilog:
	MOV   X9, X2
	RET

// func readVLENB() uint64
TEXT ·readVLENB(SB), 4, $0-8
	WORD  $0xc2202573 // csrr a0, vlenb
	MOV   X10, ret+0(FP)
	RET
