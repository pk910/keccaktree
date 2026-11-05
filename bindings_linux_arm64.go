//go:build cgo && linux && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// link to the static library via cgo
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX): Apple M-series, Graviton 3+, Neoverse V1/N2+.
var hasSHA3 = cpuid.CPU.Supports(cpuid.SHA3)

// armLazy and armN1 pick the lazy-rotation kernels (sha3_x3 with FEAT_SHA3,
// scalar_x1 without) on Arm Ltd cores; see keccaktree_arm_select in
// src/keccaktree.c. cpuid only knows the MIDR when the kernel exposes it.
var armLazy, armN1 = armSelect(cpuid.CPU.VendorID, (cpuid.CPU.Model>>4)&0xfff)

func armSelect(vendor cpuid.Vendor, part int) (lazy, n1 bool) {
	return vendor == cpuid.ARM, vendor == cpuid.ARM && part == 0xd0c
}

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; hasSHA3 / armLazy / armN1 only select faster paths.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
}
