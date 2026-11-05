//go:build darwin && arm64

// Package cgo links the prebuilt static keccaktree library for this platform.
package cgo

/*
#cgo LDFLAGS: -L${SRCDIR}/../lib/darwin_arm64 -lkeccaktree
*/
import "C"
