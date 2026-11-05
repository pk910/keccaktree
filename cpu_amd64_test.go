//go:build cgo && (linux || windows) && amd64

package keccaktree

import (
	"testing"

	"github.com/klauspost/cpuid/v2"
)

func TestAVX512SinglePort(t *testing.T) {
	for _, c := range []struct {
		v    cpuid.Vendor
		f, m int
		want bool
	}{
		{cpuid.Intel, 6, 0x7e, true},  // Ice Lake client
		{cpuid.Intel, 6, 0x8c, true},  // Tiger Lake
		{cpuid.Intel, 6, 0x55, false}, // Skylake-SP / Cascade Lake
		{cpuid.Intel, 6, 0x8f, false}, // Sapphire Rapids
		{cpuid.AMD, 25, 0x61, false},  // Zen 4
	} {
		if got := avx512SinglePort(c.v, c.f, c.m); got != c.want {
			t.Errorf("avx512SinglePort(%v, %d, %#x) = %v, want %v", c.v, c.f, c.m, got, c.want)
		}
	}
}
