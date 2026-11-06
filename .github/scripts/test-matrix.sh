#!/usr/bin/env bash
#
# Cross-architecture / cross-CPU-feature test matrix for the Go bindings.
#
# Cross-compiles a statically linked cgo test binary per Linux target (linking
# lib/<platform>/libkeccaktree.a) and runs it under qemu-user with several -cpu
# models, so every runtime-detected path (and the pure-Go fallback) runs on one
# host. KECCAKTREE_EXPECT_PATH makes the binary assert which path it selected.
#
# NOTE: qemu-user (TCG) cannot emulate AVX-512; that path runs natively.

set -u
cd "$(cd "$(dirname "$0")/../.." && pwd)"

LDFLAGS='-linkmode external -extldflags "-static"'
BIN_DIR="$(mktemp -d)"
fail=0

build() { # arch cc
	local arch="$1" cc="$2"
	echo ">> building $arch test binary"
	if ! CGO_ENABLED=1 GOOS=linux GOARCH="$arch" CC="$cc" \
		go test -c -ldflags "$LDFLAGS" -o "$BIN_DIR/$arch.test" .; then
		echo "BUILD FAIL $arch"
		fail=1
	fi
}

run() { # arch qemu cpu expect
	local arch="$1" qemu="$2" cpu="$3" expect="$4"
	local log="$BIN_DIR/$arch.log"
	KECCAKTREE_EXPECT_PATH="$expect" "$qemu" -cpu "$cpu" "$BIN_DIR/$arch.test" \
		-test.run 'TestHash|TestZeroHashChain|TestErrors|TestForcedPaths|TestActivePathMatchesEnv' \
		>"$log" 2>&1
	local rc=$?
	if [ $rc -eq 0 ]; then
		printf '  PASS  %-8s %-14s -> %s\n' "$arch" "$cpu" "$expect"
	else
		printf '  FAIL  %-8s %-14s -> %s\n' "$arch" "$cpu" "$expect"
		grep -E '^(---|    |FAIL|panic|SIGILL|SIGSEGV)' "$log" | head -10 | sed 's/^/        /'
		fail=1
	fi
}

go version
build amd64 gcc
build arm64 aarch64-linux-gnu-gcc

echo "=== matrix ==="
run amd64 qemu-x86_64  'qemu64'     generic
run amd64 qemu-x86_64  'Haswell'    avx2_x8
run arm64 qemu-aarch64 'cortex-a57' neon_x2
run arm64 qemu-aarch64 'max'        sha3_x2
run arm64 qemu-aarch64 'neoverse-n1' scalar_x1
run arm64 qemu-aarch64 'neoverse-n2' sha3_x3

echo "=== result: $([ $fail -eq 0 ] && echo ALL GREEN || echo FAILURES) ==="
exit $fail
