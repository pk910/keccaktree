//go:build cgo && linux && riscv64

package keccaktree

import (
	// links the static library; Detect runs its kernel selection
	ktcgo "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// The RISC-V kernels, in the order wrapper_linux_riscv64.s tests rvKernel.
const (
	rvRV64 uint8 = iota // base RV64I scalar
	rvZbb               // scalar with Zbb
	rvRVV               // RVV 1.0
	rvZvkb              // RVV 1.0 + Zvkb
)

var rvKernelNames = [...]string{"rv64_x1", "zbb_x1", "rvv", "rvv_zvkb"}

// rvKernel is the kernel the wrapper calls. Which of the kernels the
// extensions allow is fastest depends on VLEN and the core, so init takes
// the choice of the C library's detection, which probes riscv_hwprobe and
// times the candidates once (keccaktree_detect in src/keccaktree.c).
var rvKernel = rvRV64

func init() {
	// rv64_x1 runs on every RV64 core, so the native path is always usable.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
	detected := ktcgo.Detect()
	for i, name := range rvKernelNames {
		if name == detected {
			rvKernel = uint8(i)
		}
	}
}
