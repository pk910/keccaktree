//go:build cgo && darwin && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// links the static library; Detect runs its kernel selection
	ktcgo "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX), from the hw.optional sysctls.
var hasSHA3 = cpuid.CPU.Supports(cpuid.SHA3)

// The kernels KeccaktreeHash can call: the values are the ones
// wrapper_arm64.s switches on (its KERNEL_* defines), the names the ones
// cgo.Detect returns. Which supported kernel is fastest depends on the
// core, not on a feature bit, so init takes the choice of the C library's
// detection, which times them once (keccaktree_detect in src/keccaktree.c).
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

// kernelByName maps a cgo.Detect name to the wrapper's kernel id. A name
// the wrapper does not know (a kernel added to the C library but not
// wired here yet) falls back to the widest kernel of the feature tier.
func kernelByName(name string) uint8 {
	for id, n := range kernelNames {
		if n == name {
			return uint8(id)
		}
	}
	if hasSHA3 {
		return kernelSha3X2
	}
	return kernelNeonX2
}

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; the id only selects faster paths.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
	kernel = kernelByName(ktcgo.Detect())
}
