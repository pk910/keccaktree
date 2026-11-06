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
	case avx2X4:
		return "avx2_x4"
	default:
		return "avx2_x8"
	}
}

func forceAMD64(supported, avx512, avx2, ymm, x4 bool) func() func() {
	return func() func() {
		s, a5, a2, y, q := supportedCPU, hasAVX512, hasAVX2, avx512YMM, avx2X4
		supportedCPU, hasAVX512, hasAVX2, avx512YMM, avx2X4 = supported, avx512, avx2, ymm, x4
		return func() { supportedCPU, hasAVX512, hasAVX2, avx512YMM, avx2X4 = s, a5, a2, y, q }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceAMD64(false, false, false, false, false)},
	{"avx2_x8", hasAVX2, forceAMD64(true, false, true, false, false)},
	{"avx2_x4", hasAVX2, forceAMD64(true, false, true, false, true)},
	{"avx512_x8", hasAVX512, forceAMD64(true, true, false, false, false)},
	{"avx512vl_x4", hasAVX512, forceAMD64(true, true, false, true, false)},
}
