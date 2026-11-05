//go:build cgo && (linux || windows) && amd64

package keccaktree

// activePath mirrors the precedence in wrapper_*_amd64.s (avx512 > avx2) and
// the supportedCPU gate.
func activePath() string {
	switch {
	case !supportedCPU:
		return "generic"
	case hasAVX512:
		return "avx512_x8"
	default:
		return "avx2_x4"
	}
}

func forceAMD64(supported, avx512, avx2 bool) func() func() {
	return func() func() {
		s, a5, a2 := supportedCPU, hasAVX512, hasAVX2
		supportedCPU, hasAVX512, hasAVX2 = supported, avx512, avx2
		return func() { supportedCPU, hasAVX512, hasAVX2 = s, a5, a2 }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceAMD64(false, false, false)},
	{"avx2_x4", hasAVX2, forceAMD64(true, false, true)},
	{"avx512_x8", hasAVX512, forceAMD64(true, true, false)},
}
