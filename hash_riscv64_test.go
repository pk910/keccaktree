//go:build cgo && linux && riscv64

package keccaktree

import "golang.org/x/sys/unix"

// activePath mirrors wrapper_linux_riscv64.s (rv64_x1 runs everywhere, so
// supportedCPU is always true).
func activePath() string {
	if !supportedCPU {
		return "generic"
	}
	return rvKernelNames[rvKernel]
}

func forceRISCV64(supported bool, kernel uint8) func() func() {
	return func() func() {
		s, k := supportedCPU, rvKernel
		supportedCPU, rvKernel = supported, kernel
		return func() { supportedCPU, rvKernel = s, k }
	}
}

// the extension kernels only run where rvDetect found what they need
var forcedCases = []forcedCase{
	{"generic", true, forceRISCV64(false, rvRV64)},
	{"rv64_x1", true, forceRISCV64(true, rvRV64)},
	{"zbb_x1", rvHas(rvZbb), forceRISCV64(true, rvZbb)},
	{"rvv", rvHas(rvRVV), forceRISCV64(true, rvRVV)},
	{"rvv_zvkb", rvHas(rvZvkb), forceRISCV64(true, rvZvkb)},
}

// rvHas reports whether this CPU can run kernel k.
func rvHas(k uint8) bool {
	pairs := []unix.RISCVHWProbePairs{{Key: unix.RISCV_HWPROBE_KEY_IMA_EXT_0}}
	if unix.RISCVHWProbe(pairs, nil, 0) != nil || pairs[0].Key != unix.RISCV_HWPROBE_KEY_IMA_EXT_0 {
		return k == rvRV64
	}
	ext := pairs[0].Value
	switch k {
	case rvZbb:
		return ext&unix.RISCV_HWPROBE_EXT_ZBB != 0
	case rvRVV:
		return ext&unix.RISCV_HWPROBE_IMA_V != 0
	case rvZvkb:
		return ext&unix.RISCV_HWPROBE_IMA_V != 0 && ext&unix.RISCV_HWPROBE_EXT_ZVKB != 0
	}
	return true
}
