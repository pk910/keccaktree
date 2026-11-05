//go:build linux && amd64

// Package cgo links the prebuilt static keccaktree library for this platform.
package cgo

/*
#cgo LDFLAGS: -L${SRCDIR}/../lib/linux_amd64 -lkeccaktree
*/
import "C"
