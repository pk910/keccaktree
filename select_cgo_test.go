//go:build cgo && ((linux && amd64) || (windows && amd64) || (linux && arm64) || (darwin && arm64) || (linux && riscv64))

package keccaktree

import (
	"testing"

	ktcgo "github.com/pk910/keccaktree/cgo"
)

// The Go bindings and the C library select the kernel by the same rules,
// written twice (bindings_*.go / select_amd64.go and keccaktree_detect in
// src/keccaktree.c): on the CPU the test runs on they must agree.
func TestSelectionMatchesC(t *testing.T) {
	if got, want := activePath(), ktcgo.Detect(); got != want {
		t.Fatalf("Go selects %q, keccaktree_detect %q", got, want)
	}
}
