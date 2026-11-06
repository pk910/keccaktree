#!/usr/bin/env bash
# Builds the JNI library for one platform from the committed static library
# lib/<platform>/libkeccaktree.a, into java/native/<os>-<arch>/ (packaged into
# the jar by pom.xml).
#
#   java/build-native.sh [platform]     platform: linux_amd64 (default: host),
#                                       linux_arm64, darwin_arm64, windows_amd64
#
# CC overrides the compiler (e.g. CC=aarch64-linux-gnu-gcc for linux_arm64).
# JAVA_HOME must point at a JDK (for jni.h).
set -euo pipefail
cd "$(dirname "$0")"
root=..

host_platform() {
    local os arch
    case "$(uname -s)" in
        Linux) os=linux ;;
        Darwin) os=darwin ;;
        MINGW* | MSYS* | CYGWIN*) os=windows ;;
        *) echo "unsupported OS $(uname -s)" >&2; exit 1 ;;
    esac
    case "$(uname -m)" in
        x86_64 | amd64) arch=amd64 ;;
        aarch64 | arm64) arch=arm64 ;;
        *) echo "unsupported CPU $(uname -m)" >&2; exit 1 ;;
    esac
    echo "${os}_${arch}"
}

platform=${1:-$(host_platform)}
lib="$root/lib/$platform/libkeccaktree.a"
[ -f "$lib" ] || { echo "missing $lib" >&2; exit 1; }
: "${JAVA_HOME:?set JAVA_HOME to a JDK}"
jdk=$JAVA_HOME
command -v cygpath >/dev/null && jdk=$(cygpath -u "$JAVA_HOME")

out="native/${platform/_/-}"
mkdir -p "$out"
cflags=(-O2 -Wall -Werror -fPIC -I"$root/src" -I"$jdk/include")
case "$platform" in
    linux_*)
        cc=${CC:-gcc}
        "$cc" "${cflags[@]}" -I"$jdk/include/linux" -shared -s -Wl,-z,noexecstack -Wl,--no-undefined \
            -o "$out/libkeccaktree_jni.so" src/main/c/keccaktree_jni.c "$lib"
        ;;
    darwin_*)
        cc=${CC:-cc}
        "$cc" "${cflags[@]}" -I"$jdk/include/darwin" -dynamiclib -mmacosx-version-min=11.0 \
            -o "$out/libkeccaktree_jni.dylib" src/main/c/keccaktree_jni.c "$lib"
        ;;
    windows_*)
        cc=${CC:-gcc}
        "$cc" "${cflags[@]}" -I"$jdk/include/win32" -shared -s -static-libgcc \
            -o "$out/keccaktree_jni.dll" src/main/c/keccaktree_jni.c "$lib"
        ;;
    *) echo "unknown platform $platform" >&2; exit 1 ;;
esac
ls -l "$out"
