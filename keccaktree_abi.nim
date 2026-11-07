# keccaktree nim bindings
# Licensed under the MIT license (see LICENSE in the repository root).
#
# Low-level ABI for keccaktree, laid out like hashtree's `hashtree_abi`.
# `keccaktree_hash` has the same signature and chunk layout as
# `hashtree_hash`, with Ethereum keccak256 (pad 0x01) in place of SHA-256:
#
#   digest[i] = keccak256(input[64*i ..< 64*i+64])
#
# On linux amd64/arm64/riscv64, macOS arm64 and Windows amd64 this links the CI-built,
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
    elif defined(linux) and defined(riscv64): "linux_riscv64"
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
    (defined(amd64) or defined(arm64) or defined(riscv64))

  when keccaktreeAsm:
    const asmDir = srcDir
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
      {.compile(asmDir & "keccak256_avx512_x9.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx512vl_x4d.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx512_x8d.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx512_x9d.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x8.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x4.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x9.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x10.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x5.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x6.S", asmFlags).}
      {.compile(asmDir & "keccak256_avx2_x2.S", asmFlags).}
      {.compile(asmDir & "keccak256_x86_x1.S", asmFlags).}
    elif defined(arm64):
      {.compile(asmDir & "keccak256_neon_x2.S", asmFlags).}
      {.compile(asmDir & "keccak256_neon_x3.S", asmFlags).}
      {.compile(asmDir & "keccak256_sha3_x2.S", asmFlags).}
      {.compile(asmDir & "keccak256_scalar_x1.S", asmFlags).}
      {.compile(asmDir & "keccak256_sha3_x3.S", asmFlags).}
      {.compile(asmDir & "keccak256_sha3_x3r.S", asmFlags).}
    elif defined(riscv64):
      {.compile(asmDir & "keccak256_rv64_x1.S", asmFlags).}
      {.compile(asmDir & "keccak256_zbb_x1.S", asmFlags).}
      {.compile(asmDir & "keccak256_rvv.S", asmFlags).}
      {.compile(asmDir & "keccak256_rvv_zvkb.S", asmFlags).}

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
  # avx2_x4 / avx2_x8 with one or two extra nodes in the integer registers
  # (AVX2 + BMI1 + BMI2)
  func keccaktree_keccak256_avx2_x5*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx2_x6*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx2_x9*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx2_x10*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  # the AVX2 kernels' tails: lane pairs for 2 remaining nodes (when
  # keccaktree_avx2_small_tail(2) enables them, as detection does where
  # they win), one node in the integer registers (BMI1 + BMI2)
  func keccaktree_keccak256_avx2_x2*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_x86_x1*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  proc keccaktree_avx2_small_tail*(max: uint64) {.keccaktreedecl.}
  # 5..max remaining nodes of avx2_x10/x9 go to avx2_x5 (4..9), the rest run
  # as a padded batch; detection times both and sets it
  proc keccaktree_avx2_x10_mid_tail*(max: uint64) {.keccaktreedecl.}
  func keccaktree_keccak256_avx512vl_x4*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx512_x8*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  # avx512_x8 with one extra node in the integer registers (AVX-512F/VL +
  # BMI1 + BMI2)
  func keccaktree_keccak256_avx512_x9*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  # the same three with the D-form rounds (all lanes in registers; AMD)
  func keccaktree_keccak256_avx512vl_x4d*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx512_x8d*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_avx512_x9d*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}

when keccaktreeAsm and defined(arm64):
  func keccaktree_keccak256_neon_x2*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_scalar_x1*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  # neon_x2 interleaved with scalar_x1
  func keccaktree_keccak256_neon_x3*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  # FEAT_SHA3 only
  func keccaktree_keccak256_sha3_x2*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_sha3_x3*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_sha3_x3r*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}

when keccaktreeAsm and defined(riscv64):
  func keccaktree_keccak256_rv64_x1*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  # Zbb, V, V + Zvkb only
  func keccaktree_keccak256_zbb_x1*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_rvv*(output: pointer, input: pointer, count: uint64) {.
    keccaktreedecl.}
  func keccaktree_keccak256_rvv_zvkb*(output: pointer, input: pointer, count: uint64) {.
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
