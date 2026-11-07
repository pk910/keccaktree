//go:build cgo && arm64

// The C kernels run below this frame on its 2048 bytes of stack. The
// kernel is the one the C library's detection picked (bindings_*_arm64.go).
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
	RET

sha3x3:
	BL keccaktree_keccak256_sha3_x3(SB)
	RET

sha3x3r:
	BL keccaktree_keccak256_sha3_x3r(SB)
	RET

sha3x2:
	BL keccaktree_keccak256_sha3_x2(SB)
	RET

neonx3:
	BL keccaktree_keccak256_neon_x3(SB)
	RET

scalar:
	BL keccaktree_keccak256_scalar_x1(SB)
	RET
