//go:build cgo && darwin && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// links the static library
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX), from the hw.optional sysctls.
var hasSHA3 = cpuid.CPU.Supports(cpuid.SHA3)

// The kernels KeccaktreeHash can call: the values are the ones
// wrapper_arm64.s switches on (its KERNEL_* defines), the names those of
// the C library (keccaktree_keccak256_<name>).
const (
	kernelNeonX2 uint8 = iota // also the wrapper's default
	kernelNeonX3
	kernelScalarX1
	kernelSha3X2
	kernelSha3X3
	kernelSha3X3r
)

var kernelNames = [...]string{
	kernelNeonX2:   "neon_x2",
	kernelNeonX3:   "neon_x3",
	kernelScalarX1: "scalar_x1",
	kernelSha3X2:   "sha3_x2",
	kernelSha3X3:   "sha3_x3",
	kernelSha3X3r:  "sha3_x3r",
}

// kernel is the one KeccaktreeHash calls, read by the wrapper.
var kernel uint8

// selectKernel is keccaktree_detect of src/keccaktree.c for macOS: Apple
// cores run an EOR/BIC with a rotated operand at a lower rate, so they get
// sha3_x3r, the hybrid with explicit rotations (M1: 66 ns per node against
// 77 for sha3_x2). Nothing is run or timed.
func selectKernel(sha3 bool) uint8 {
	if sha3 {
		return kernelSha3X3r
	}
	return kernelNeonX2
}

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; the id only selects faster paths.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
	kernel = selectKernel(hasSHA3)
}
