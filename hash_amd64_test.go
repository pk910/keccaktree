//go:build cgo && (linux || windows) && amd64

package keccaktree

// activePath mirrors the precedence in wrapper_*_amd64.s (avx512 > avx2) and
// the supportedCPU gate.
func activePath() string {
	switch {
	case !supportedCPU:
		return "generic"
	case hasAVX512 && avx512YMM:
		return "avx512vl_x4"
	case hasAVX512:
		return "avx512_x8"
	default:
		return "avx2_x8"
	}
}

func forceAMD64(supported, avx512, avx2, ymm bool) func() func() {
	return func() func() {
		s, a5, a2, y := supportedCPU, hasAVX512, hasAVX2, avx512YMM
		supportedCPU, hasAVX512, hasAVX2, avx512YMM = supported, avx512, avx2, ymm
		return func() { supportedCPU, hasAVX512, hasAVX2, avx512YMM = s, a5, a2, y }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceAMD64(false, false, false, false)},
	{"avx2_x8", hasAVX2, forceAMD64(true, false, true, false)},
	{"avx512_x8", hasAVX512, forceAMD64(true, true, false, false)},
	{"avx512vl_x4", hasAVX512, forceAMD64(true, true, false, true)},
}
