//go:build cgo && arm64

// The C kernels run on this frame's 2048 bytes of stack (deepest: neon_x3,
// 208 bytes): RSP is moved to the top of the frame around the call. Called
// at the frame's own RSP, a kernel's frame would start right below it and
// cover the word at RSP-8, where Go keeps the caller's frame pointer:
// neon_x2, neon_x3 and scalar_x1 spill a lane there, and R29 came back as
// keccak state. The kernel is the one bindings_*_arm64.go selected from
// the CPU's features.
//
// Kernel ids, as in bindings_*_arm64.go (kernelNeonX2 is the default).
#define KERNEL_NEON_X3   1
#define KERNEL_SCALAR_X1 2
#define KERNEL_SHA3_X2   3
#define KERNEL_SHA3_X3   4
#define KERNEL_SHA3_X3R  5

TEXT ·KeccaktreeHash(SB), 0, $2048-24
	MOVD output+0(FP), R0
	MOVD input+8(FP), R1
	MOVD count+16(FP), R2
	ADD  $2048, RSP

	MOVBU ·kernel(SB), R19
	CMPW  $KERNEL_SHA3_X3, R19
	BEQ   sha3x3
	CMPW  $KERNEL_SHA3_X3R, R19
	BEQ   sha3x3r
	CMPW  $KERNEL_SHA3_X2, R19
	BEQ   sha3x2
	CMPW  $KERNEL_NEON_X3, R19
	BEQ   neonx3
	CMPW  $KERNEL_SCALAR_X1, R19
	BEQ   scalar
	BL    keccaktree_keccak256_neon_x2(SB)
	B     epilog

sha3x3:
	BL keccaktree_keccak256_sha3_x3(SB)
	B  epilog

sha3x3r:
	BL keccaktree_keccak256_sha3_x3r(SB)
	B  epilog

sha3x2:
	BL keccaktree_keccak256_sha3_x2(SB)
	B  epilog

neonx3:
	BL keccaktree_keccak256_neon_x3(SB)
	B  epilog

scalar:
	BL keccaktree_keccak256_scalar_x1(SB)

epilog:
	SUB $2048, RSP
	RET
