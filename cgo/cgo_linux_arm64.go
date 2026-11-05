//go:build linux && arm64

// Package cgo links the prebuilt static keccaktree library for this platform.
package cgo

/*
#cgo LDFLAGS: -L${SRCDIR}/../lib/linux_arm64 -lkeccaktree
*/
import "C"
