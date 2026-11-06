//go:build cgo && linux && riscv64

package keccaktree

import (
	"golang.org/x/sys/unix"

	// link to the static library via cgo
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// readVLENB returns the vector register size in bytes (csrr vlenb); only
// call it when the kernel reports V.
func readVLENB() uint64

// The RISC-V kernels, in the order wrapper_linux_riscv64.s tests rvKernel.
const (
	rvRV64 uint8 = iota // base RV64I scalar
	rvZbb               // scalar with Zbb
	rvRVV               // RVV 1.0
	rvZvkb              // RVV 1.0 + Zvkb
)

var rvKernelNames = [...]string{"rv64_x1", "zbb_x1", "rvv", "rvv_zvkb"}

// rvKernel is the kernel the wrapper calls, picked as in
// keccaktree_riscv_select (src/keccaktree.c) from riscv_hwprobe.
var rvKernel = rvDetect()

func rvDetect() uint8 {
	pairs := []unix.RISCVHWProbePairs{{Key: unix.RISCV_HWPROBE_KEY_IMA_EXT_0}}
	var ext, vlenb uint64
	if unix.RISCVHWProbe(pairs, nil, 0) == nil && pairs[0].Key == unix.RISCV_HWPROBE_KEY_IMA_EXT_0 {
		ext = pairs[0].Value
	}
	if ext&unix.RISCV_HWPROBE_IMA_V != 0 {
		vlenb = readVLENB()
	}
	return rvSelect(ext, vlenb)
}

// rvSelect mirrors keccaktree_riscv_select: the vector kernels with Zvkb at
// any VLEN, without Zvkb from VLEN = 256 on (or when there is no Zbb).
func rvSelect(ext, vlenb uint64) uint8 {
	v := ext&unix.RISCV_HWPROBE_IMA_V != 0 && vlenb >= 16
	switch {
	case v && ext&unix.RISCV_HWPROBE_EXT_ZVKB != 0:
		return rvZvkb
	case v && vlenb >= 32:
		return rvRVV
	case ext&unix.RISCV_HWPROBE_EXT_ZBB != 0:
		return rvZbb
	case v:
		return rvRVV
	default:
		return rvRV64
	}
}

func init() {
	// rv64_x1 runs on every RV64 core, so the native path is always usable.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
}
