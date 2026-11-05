//go:build cgo && windows && amd64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// link to the static library via cgo
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// The AVX-512 path also uses the 256-bit (VL) encodings for short tails.
var hasAVX512 = cpuid.CPU.Supports(cpuid.AVX512F, cpuid.AVX512VL)
var hasAVX2 = cpuid.CPU.Supports(cpuid.AVX2)

// avx512YMM selects the 256-bit avx512vl_x4 kernel over avx512_x8 on Intel
// client cores whose 512-bit integer ops issue on a single port (see
// keccaktree_avx512_single_port in src/keccaktree.c).
var avx512YMM = hasAVX512 && avx512SinglePort(cpuid.CPU.VendorID, cpuid.CPU.Family, cpuid.CPU.Model)

func init() {
	supportedCPU = hasAVX2 || hasAVX512
	keccaktreeHash = KeccaktreeHash
}
