//go:build cgo && (linux || windows) && amd64

package keccaktree

// activePath mirrors wrapper_*_amd64.s: the kernel id picked by init, behind
// the supportedCPU gate.
func activePath() string {
	if !supportedCPU {
		return "generic"
	}
	return kernelNames[kernel]
}

func forceAMD64(supported bool, k uint8) func() func() {
	return func() func() {
		s, id := supportedCPU, kernel
		supportedCPU, kernel = supported, k
		return func() { supportedCPU, kernel = s, id }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceAMD64(false, kernelAVX2X8)},
	{"avx2_x8", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X8)},
	{"avx2_x4", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X4)},
	{"avx2_x5", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X5)},
	{"avx2_x6", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X6)},
	{"avx2_x9", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X9)},
	{"avx2_x10", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X10)},
	{"x86_x1", hasBMI, forceAMD64(true, kernelX86X1)},
	{"avx512_x8", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512X8)},
	{"avx512_x9", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512X9)},
	{"avx512vl_x4", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512VLX4)},
}
