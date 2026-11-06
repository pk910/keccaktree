#!/usr/bin/env bash
#
# TEMPORARY PR LIBRARIES ONLY. Builds lib/<platform>/libkeccaktree.a for all
# four platforms on one host with zig's cross-compiling clang, so a pull
# request that changes src/ can carry matching libraries and its Go binding
# tests pass. Zig is not the project's build system: after the merge,
# "Update Static Libraries" rebuilds every library on main with the native
# toolchains (gcc, Apple clang, MSYS2 gcc) and attests it, replacing these.
#
#   .github/scripts/build-libs.sh
#
# Needs zig (https://ziglang.org, or `pip install ziglang`), llvm-ar and
# llvm-ranlib. Alternatively, .github/scripts/fetch-ci-libs.sh copies the
# artifacts of a "Build & Test" run on your branch.

set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"

if command -v zig >/dev/null; then zig=(zig)
elif python3 -c 'import ziglang' 2>/dev/null; then zig=(python3 -m ziglang)
else echo "zig not found (install it, or: pip install ziglang)" >&2; exit 1; fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
printf '#!/bin/sh\nexec %s cc -target "$KT_ZIG_TARGET" "$@"\n' "${zig[*]}" > "$work/cc"
chmod +x "$work/cc"

export SOURCE_DATE_EPOCH="$(git log -1 --format=%ct)"
zig_version="$("${zig[@]}" version)"

build() { # platform zig-target ar-format
	local platform="$1" target="$2" format="$3" out="$work/$1"
	echo ">> $platform ($target)"
	KT_ZIG_TARGET="$target" make -s -C src OUT_DIR="$out" CC="$work/cc" \
		AR="llvm-ar --format=$format" \
		CFLAGS="-O3 -Wall -Werror -ffile-prefix-map=$root/src=." \
		"$out/lib/libkeccaktree.a"
	cp "$out/lib/libkeccaktree.a" "lib/$platform/"
	(
		cd "lib/$platform"
		llvm-ranlib libkeccaktree.a
		echo "zig cc $zig_version -target $target (temporary PR build, replaced on merge)" > libkeccaktree.a.buildinfo
		sha256sum libkeccaktree.a > libkeccaktree.a.sha256
	)
}

build linux_amd64   x86_64-linux-gnu    gnu
build linux_arm64   aarch64-linux-gnu   gnu
build darwin_arm64  aarch64-macos.11.0  darwin
build windows_amd64 x86_64-windows-gnu  gnu
git rev-parse HEAD > lib/SOURCE_COMMIT
echo "lib/ rebuilt for $(git rev-parse --short HEAD); commit it with your change"
