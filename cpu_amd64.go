//go:build cgo && (linux || windows) && amd64

package keccaktree

import "github.com/klauspost/cpuid/v2"

// avx512SinglePort reports Intel client cores with AVX-512 (Cannon, Ice,
// Tiger and Rocket Lake), which run 512-bit integer ops on one port only
// while 256-bit ops still use three.
func avx512SinglePort(vendor cpuid.Vendor, family, model int) bool {
	if vendor != cpuid.Intel || family != 6 {
		return false
	}
	switch model {
	case 0x66, 0x7d, 0x7e, 0x8c, 0x8d, 0xa7:
		return true
	}
	return false
}
