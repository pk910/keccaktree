# keccaktree nim bindings: every kernel this CPU supports, checked against a
# reference keccak256 for 0..300 nodes, unaligned buffers and in-place use.

import std/strutils
import ../../keccaktree_abi

# CPU feature checks for the direct kernel calls (the library does its own)
{.emit: """
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
static int kt_cpu(int f) {
  __builtin_cpu_init();
  return f == 1 ? __builtin_cpu_supports("avx2")
       : f == 2 ? __builtin_cpu_supports("avx512f") && __builtin_cpu_supports("avx512vl")
       : 0;
}
#elif defined(__aarch64__) && defined(__APPLE__)
static int kt_cpu(int f) { return f == 3; }
#elif defined(__aarch64__) && defined(__linux__)
#include <sys/auxv.h>
static int kt_cpu(int f) { return f == 3 && (getauxval(AT_HWCAP) & (1UL << 17)); }
#else
static int kt_cpu(int f) { (void)f; return 0; }
#endif
""".}
proc kt_cpu(f: cint): cint {.importc, nodecl.}

const
  RC = [0x0000000000000001'u64, 0x0000000000008082'u64, 0x800000000000808A'u64,
        0x8000000080008000'u64, 0x000000000000808B'u64, 0x0000000080000001'u64,
        0x8000000080008081'u64, 0x8000000000008009'u64, 0x000000000000008A'u64,
        0x0000000000000088'u64, 0x0000000080008009'u64, 0x000000008000000A'u64,
        0x000000008000808B'u64, 0x800000000000008B'u64, 0x8000000000008089'u64,
        0x8000000000008003'u64, 0x8000000000008002'u64, 0x8000000000000080'u64,
        0x000000000000800A'u64, 0x800000008000000A'u64, 0x8000000080008081'u64,
        0x8000000000008080'u64, 0x0000000080000001'u64, 0x8000000080008008'u64]
  rotc = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43,
          62, 18, 39, 61, 20, 44]
  piln = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2,
          20, 14, 22, 9, 6, 1]

func rotl(x: uint64, n: int): uint64 = (x shl n) or (x shr (64 - n))

func keccakF(st: var array[25, uint64]) =
  var bc: array[5, uint64]
  for r in 0 ..< 24:
    for i in 0 ..< 5:
      bc[i] = st[i] xor st[i + 5] xor st[i + 10] xor st[i + 15] xor st[i + 20]
    for i in 0 ..< 5:
      let t = bc[(i + 4) mod 5] xor rotl(bc[(i + 1) mod 5], 1)
      for j in countup(0, 20, 5):
        st[j + i] = st[j + i] xor t
    var t = st[1]
    for i in 0 ..< 24:
      let j = piln[i]
      let tmp = st[j]
      st[j] = rotl(t, rotc[i])
      t = tmp
    for j in countup(0, 20, 5):
      for i in 0 ..< 5:
        bc[i] = st[j + i]
      for i in 0 ..< 5:
        st[j + i] = st[j + i] xor ((not bc[(i + 1) mod 5]) and bc[(i + 2) mod 5])
    st[0] = st[0] xor RC[r]

func referenceNode(input: openArray[byte], output: var openArray[byte]) =
  ## keccak256 of exactly 64 bytes (one block, rate 136, pad 0x01 .. 0x80)
  var st: array[25, uint64]
  for lane in 0 ..< 8:
    for b in 0 ..< 8:
      st[lane] = st[lane] or (uint64(input[lane * 8 + b]) shl (8 * b))
  st[8] = st[8] xor 0x01'u64
  st[16] = st[16] xor 0x8000000000000000'u64
  keccakF(st)
  for i in 0 ..< 32:
    output[i] = byte((st[i div 8] shr (8 * (i mod 8))) and 0xff)

proc reference(input: openArray[byte], nodes: int): seq[byte] =
  result = newSeq[byte](nodes * 32)
  for n in 0 ..< nodes:
    referenceNode(input.toOpenArray(n * 64, n * 64 + 63),
                  result.toOpenArray(n * 32, n * 32 + 31))

proc makeInput(nodes, offset: int): seq[byte] =
  ## one spare byte, so that the first node has an address even for 0 nodes
  result = newSeq[byte](nodes * 64 + offset + 1)
  var x = 0x9e3779b9'u32 xor uint32(nodes)
  for b in result.mitems:
    x = x xor (x shl 13)
    x = x xor (x shr 17)
    x = x xor (x shl 5)
    b = byte(x and 0xff)

proc hexOf(a: openArray[byte]): string =
  for b in a: result.add b.toHex(2).toLowerAscii

type Kernel = tuple[name: string, fn: KeccaktreeHashFcn, feature: int]

proc kernels(): seq[Kernel] =
  result.add (name: "generic", fn: KeccaktreeHashFcn(keccaktree_keccak256_generic), feature: 0)
  when keccaktreeAsm and defined(amd64):
    result.add (name: "avx2_x4", fn: KeccaktreeHashFcn(keccaktree_keccak256_avx2_x4), feature: 1)
    result.add (name: "avx2_x8", fn: KeccaktreeHashFcn(keccaktree_keccak256_avx2_x8), feature: 1)
    result.add (name: "avx512vl_x4", fn: KeccaktreeHashFcn(keccaktree_keccak256_avx512vl_x4), feature: 2)
    result.add (name: "avx512_x8", fn: KeccaktreeHashFcn(keccaktree_keccak256_avx512_x8), feature: 2)
  when keccaktreeAsm and defined(arm64):
    result.add (name: "neon_x2", fn: KeccaktreeHashFcn(keccaktree_keccak256_neon_x2), feature: 0)
    result.add (name: "scalar_x1", fn: KeccaktreeHashFcn(keccaktree_keccak256_scalar_x1), feature: 0)
    result.add (name: "sha3_x2", fn: KeccaktreeHashFcn(keccaktree_keccak256_sha3_x2), feature: 3)
    result.add (name: "sha3_x3", fn: KeccaktreeHashFcn(keccaktree_keccak256_sha3_x3), feature: 3)
    result.add (name: "sha3_x3r", fn: KeccaktreeHashFcn(keccaktree_keccak256_sha3_x3r), feature: 3)

proc testReference() =
  var zero: array[64, byte]
  var digest: array[32, byte]
  referenceNode(zero, digest)
  doAssert digest.hexOf == "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5"

proc testKernels() =
  for k in kernels():
    if k.feature != 0 and kt_cpu(cint(k.feature)) == 0:
      echo "  ", k.name, " [skipped, not supported]"
      continue
    for nodes in 0 .. 300:
      for offset in [0, 1, 7]:
        let buf = makeInput(nodes, offset)
        let expect = reference(buf.toOpenArray(offset, buf.high), nodes)
        var output = newSeq[byte](nodes * 32 + offset + 1)
        k.fn(addr output[offset], unsafeAddr buf[offset], uint64(nodes))
        doAssert output[offset ..< offset + nodes * 32] == expect,
          k.name & " nodes=" & $nodes & " offset=" & $offset
    echo "  ", k.name, " [OK]"

proc testDispatch() =
  keccaktree_init(nil)
  for nodes in [0, 1, 2, 3, 5, 8, 17, 64, 255, 256]:
    var buf = makeInput(nodes, 0)
    let expect = reference(buf, nodes)
    var output = newSeq[byte](nodes * 32)
    keccaktreeHash(output, buf.toOpenArray(0, nodes * 64 - 1))
    doAssert output == expect, "dispatch nodes=" & $nodes
    keccaktree_hash(addr buf[0], addr buf[0], uint64(nodes))
    doAssert buf[0 ..< nodes * 32] == expect, "in place nodes=" & $nodes
  echo "  dispatch, in place [OK]"

proc testChunks() =
  var chunks = newSeq[array[32, byte]](34)
  for i in 0 ..< chunks.len:
    for b in chunks[i].mitems: b = byte(i)
  var digests = newSeq[array[32, byte]](17)
  keccaktreeHash(digests, chunks)
  for i in 0 ..< digests.len:
    var node: array[64, byte]
    node[0 ..< 32] = chunks[2 * i]
    node[32 ..< 64] = chunks[2 * i + 1]
    var expect: array[32, byte]
    referenceNode(node, expect)
    doAssert digests[i] == expect
  echo "  chunk pairs [OK]"

when isMainModule:
  testReference()
  testKernels()
  testDispatch()
  testChunks()
  echo "all passed"
