//go:build cgo && linux && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// links the static library
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX), from AT_HWCAP.
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

// The lazy-rotation scalar node of sha3_x3 and neon_x3 needs an EOR/BIC
// with a rotated operand at full rate: true on Arm Ltd cores (MIDR
// implementer 41H), false on Apple's, which get the explicit rotations of
// sha3_x3r. Without FEAT_SHA3 only Neoverse N1 and its client sibling
// Cortex-A76 (parts D0CH, D0BH) were measured to gain from neon_x3. cpuid
// only knows the MIDR when the kernel exposes it (HWCAP_CPUID).
var armLtd = cpuid.CPU.VendorID == cpuid.ARM
var armApple = cpuid.CPU.VendorID == cpuid.Apple
var armPart = (cpuid.CPU.Model >> 4) & 0xfff

// selectKernel is keccaktree_detect of src/keccaktree.c for Linux/AArch64,
// where the measurements behind each rule are listed; the two must stay
// the same (TestSelectionMatchesC compares them on the CPU the tests run
// on). Nothing is run or timed.
func selectKernel(sha3, arm, apple bool, part int) uint8 {
	switch {
	case sha3 && arm:
		return kernelSha3X3
	case sha3 && apple:
		return kernelSha3X3r
	case sha3:
		return kernelSha3X2
	case arm && (part == 0xd0c || part == 0xd0b):
		return kernelNeonX3
	}
	return kernelNeonX2
}

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; the id only selects faster paths.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
	kernel = selectKernel(hasSHA3, armLtd, armApple, armPart)
}
