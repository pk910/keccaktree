#!/usr/bin/env bash
# Build the interleaved A/B harness: this tree's library against a frozen
# baseline built from another commit (default origin/main) whose public
# symbols are renamed base_* at compile time (-D for every name in its
# keccaktree.h; works for the C and the .S files on ELF and Mach-O alike,
# no objcopy). Output: $OUT_DIR/ab (default build/ab).
#   usage: bench/ab/build.sh [base-ref]      (CC, OUT_DIR from the environment)
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
ref="${1:-origin/main}"
out="${OUT_DIR:-$root/build}"
base="$out/base"
CC="${CC:-cc}"
rm -rf "$base" && mkdir -p "$base"
git -C "$root" archive "$ref" src | tar -x -C "$base"
defs="$(grep -o 'keccaktree_[a-z0-9_]*' "$base/src/keccaktree.h" | sort -u | sed 's/.*/-D&=base_&/' | tr '\n' ' ')"
make -s -C "$base/src" OUT_DIR="$base/build" CC="$CC" CFLAGS="-g -O3 -Wall -Werror $defs" ASFLAGS="-g $defs" lib
# every defined global of the baseline must carry the prefix now
if nm -g "$base/build/lib/libkeccaktree.a" | grep -E ' [TDBRS] _?keccaktree_'; then
    echo "unprefixed symbols in the baseline library" >&2; exit 1
fi
make -s -C "$root/src" OUT_DIR="$out" CC="$CC" lib
case "$(uname)" in
    Darwin) libs="-Wl,-force_load,$out/lib/libkeccaktree.a -Wl,-force_load,$base/build/lib/libkeccaktree.a" ;;
    *) libs="-Wl,--whole-archive $out/lib/libkeccaktree.a $base/build/lib/libkeccaktree.a -Wl,--no-whole-archive" ;;
esac
$CC -O2 -g -o "$out/ab" "$root/bench/ab/ab.c" -I"$root/src" $libs
echo "$out/ab: candidate $(git -C "$root" rev-parse --short HEAD) vs base $(git -C "$root" rev-parse --short "$ref")"
