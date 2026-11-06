# keccaktree nim bindings
# Licensed under the MIT license (see LICENSE in the repository root).
#
# Low-level ABI for keccaktree, laid out like hashtree's `hashtree_abi`.
# `keccaktree_hash` has the same signature and chunk layout as
# `hashtree_hash`, with Ethereum keccak256 (pad 0x01) in place of SHA-256:
#
#   digest[i] = keccak256(input[64*i ..< 64*i+64])
#
# On linux amd64/arm64, macOS arm64 and Windows amd64 this links the CI-built,
# attested static library from lib/<platform>/ (the one the Go bindings use).
# Elsewhere, or with -d:keccaktreeFromSource, it compiles src/ into the
# program instead.

{.pragma: keccaktreedecl, importc, cdecl, gcsafe, raises: [].}

import std/[os, strutils]

const
  rootDir = currentSourcePath.parentDir.replace('\\', '/')
  srcDir = rootDir & "/src/"
  keccaktreePlatform =
    when defined(linux) and defined(amd64): "linux_amd64"
    elif defined(linux) and defined(arm64): "linux_arm64"
    elif defined(macosx) and defined(arm64): "darwin_arm64"
    elif defined(windows) and defined(amd64): "windows_amd64"
    else: ""
  keccaktreePrebuilt = keccaktreePlatform.len > 0 and not defined(keccaktreeFromSource)

when keccaktreePrebuilt:
  const keccaktreeAsm* = true
    ## The x86-64 / AArch64 kernels below are linked.
  {.passl: quoteShell(rootDir & "/lib/" & keccaktreePlatform & "/libkeccaktree.a").}
else:
  {.compile: srcDir & "keccaktree.c".}
  {.compile: srcDir & "keccak256_generic.c".}

  # The kernels are GNU assembler syntax, which gcc and clang (also its
  # integrated assembler, on ELF and Mach-O) accept and MSVC does not.
  const keccaktreeAsm* = (defined(gcc) or defined(clang)) and
    (defined(amd64) or defined(arm64))

  when keccaktreeAsm:
    const asmDir = srcDir & "asm/"
    const asmFlags =
      when defined(windows) and defined(gcc):
        # as in src/Makefile: gcc on Windows does not realign the stack for
        # 32/64-byte vector spills
        "-Wa,-muse-unaligned-vector-move"
      else:
        ""

    when defined(amd64):
      {.compile(asmDir & "keccak256_avx512_x8.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx512vl_x4.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x4.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x8.S", asmFlags).}
    elif defined(arm64):
      {.compile(asmDir & "keccak256_neon_x2.S", asmFlags).}
      {.compile(asmDir & "keccak256_sha3_x2.S", asmFlags).}
      {.compile(asmDir & "keccak256_scalar_x1.S", asmFlags).}
      {.compile(asmDir & "keccak256_sha3_x3.S", asmFlags).}
      {.compile(asmDir & "keccak256_sha3_x3r.S", asmFlags).}

type KeccaktreeHashFcn* = proc(output: pointer, input: pointer, count: uint64) {.
  cdecl, noSideEffect, gcsafe, raises: [].}

proc keccaktree_init*(override: KeccaktreeHashFcn) {.keccaktreedecl.}
  ## Selects the kernel, or detects it from the CPU when `nil`. Optional:
  ## detection also happens on the first hash call.

func keccaktree_hash*(output: pointer, input: pointer, count: uint64) {.
  keccaktreedecl.}
  ## Hashes `count` 64-byte nodes from `input` into `count` 32-byte digests
  ## in `output`. `output` may alias `input`.

func keccaktree_keccak256_generic*(output: pointer, input: pointer, count: uint64) {.
  keccaktreedecl.}

when keccaktreeAsm and defined(amd64):
  # Undefined behavior on CPUs without the instructions; keccaktree_hash
  # picks a supported one.
  func keccaktree_keccak256_avx2_x4*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx2_x8*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx512vl_x4*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx512_x8*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}

when keccaktreeAsm and defined(arm64):
  func keccaktree_keccak256_neon_x2*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_scalar_x1*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  # FEAT_SHA3 only
  func keccaktree_keccak256_sha3_x2*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_sha3_x3*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_sha3_x3r*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}

func keccaktreeHash*(output: var openArray[byte], input: openArray[byte]) =
  ## Hashes every 64-byte node of `input` into consecutive 32-byte digests
  ## in `output`.
  doAssert input.len mod 64 == 0, "input length must be a multiple of 64"
  let count = input.len div 64
  doAssert output.len >= count * 32, "output too short"
  if count > 0:
    keccaktree_hash(addr output[0], unsafeAddr input[0], count.uint64)

func keccaktreeHash*(output: var openArray[array[32, byte]],
                     chunks: openArray[array[32, byte]]) =
  ## `output[i] = keccak256(chunks[2*i] & chunks[2*i+1])`, like `Hash` in
  ## the Go bindings.
  doAssert chunks.len mod 2 == 0, "odd number of chunks"
  let count = chunks.len div 2
  doAssert output.len >= count, "output too short"
  if count > 0:
    keccaktree_hash(addr output[0], unsafeAddr chunks[0], count.uint64)
