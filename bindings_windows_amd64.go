//go:build cgo && windows && amd64

package keccaktree

import (
	// links the static library
	_ "github.com/pk910/keccaktree/cgo"
)

// KeccaktreeHash calls the kernel that select_amd64.go picked at package
// initialization from the CPU's feature bits (wrapper_windows_amd64.s).
//
//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)
