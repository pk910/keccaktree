//go:build cgo && linux && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// links the static library; Detect runs its kernel selection
	ktcgo "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX), from AT_HWCAP.
var hasSHA3 = cpuid.CPU.Supports(cpuid.SHA3)

// armLazy picks sha3_x3, armROR sha3_x3r (else sha3_x2) when hasSHA3,
// armScalar scalar_x1 and armHybrid neon_x3 over neon_x2 without it. Which supported kernel is
// fastest depends on the core, not on a feature bit, so init takes the
// choice of the C library's detection, which times them once
// (keccaktree_detect in src/keccaktree.c).
var armLazy, armROR, armScalar, armHybrid bool

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; the flags only select faster paths.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
	switch ktcgo.Detect() {
	case "sha3_x3":
		armLazy = true
	case "sha3_x3r":
		armROR = true
	case "scalar_x1":
		armScalar = true
	case "neon_x3":
		armHybrid = true
	}
}
