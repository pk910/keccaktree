# keccaktree

keccaktree is a keccak256 library optimized for Merkle tree computation. It is
a drop-in replacement for [hashtree](https://github.com/OffchainLabs/hashtree)
and its Go bindings: same calls, same chunk layout, only the hash changes from
SHA256 to Ethereum keccak256 (padding `0x01`, not NIST SHA3-256).

```c
void keccaktree_hash(unsigned char *output, const unsigned char *input, uint64_t count);
```

`input` holds `count` chunks of 64 bytes, `output` receives the `count`
32-byte digests, `digest[i] = keccak256(input[64*i .. 64*i+63])`. `output`
may alias `input` for in-place layer reduction. As in hashtree, there are no
length checks. Define `KECCAKTREE_HASHTREE_COMPAT` before including
`keccaktree.h` to get the `hashtree_*` names.

The first call picks the kernel from what the CPU reports about itself: the
feature bits (CPUID, `AT_HWCAP`, `hw.optional` sysctl, `riscv_hwprobe`) decide
which kernels can run, and where several can, the vendor, family and core type
(CPUID, `MIDR_EL1`) pick the one measured fastest on that core. Nothing is run
or timed: detection costs a few CPUID reads (about 2 µs) and gives the same
answer in every process. `keccaktree_init(fn)` sets a kernel explicitly.

On x86-64 CPUs with two kinds of cores (Intel P- and E-cores) no single AVX2
kernel fits: `avx2_x8` is 32% slower than `avx2_x6` on an E-core, `avx2_x6`
54% slower than `avx2_x8` on a P-core (Core i9-14900K). There the selected
kernel is `avx2_hybrid`, a dispatcher that reads the current logical CPU with
`rdpid` on every call and jumps to the kernel of that core's type, which it
learns from CPUID leaf 1AH the first time it sees each CPU.

| CPU | Kernel |
|---|---|
| AVX-512, AMD Zen 4 | `avx512_x9d` |
| AVX-512, Intel Ice / Tiger / Rocket Lake client | `avx512vl_x4` |
| AVX-512, Intel without AVX512-FP16 (Skylake-SP to Ice Lake server) | `avx512_x8` |
| AVX-512, everything else (Zen 5, Sapphire Rapids and later) | `avx512_x8d` |
| AVX2, P- and E-cores | `avx2_hybrid` (`avx2_x8` / `avx2_x6` per core) |
| AVX2, AMD | `avx2_x10` |
| AVX2, Intel | `avx2_x8`, Atom cores `avx2_x6` |
| AVX2, other vendors | `avx2_x5` (at most 12% behind the best kernel on Zen 3, Raptor Cove and Gracemont) |
| BMI1 + BMI2 only | `x86_x1` |
| FEAT_SHA3, Arm Ltd cores / Apple cores / others | `sha3_x3` / `sha3_x3r` / `sha3_x2` |
| AArch64, Neoverse N1 and Cortex-A76 / others | `neon_x3` / `neon_x2` |
| RISC-V | `rvv_zvkb` with Zvkb, `rvv` from VLEN 256 on, else `zbb_x1`, `rvv`, `rv64_x1` |

## Kernels

All kernels are hand-written assembly in `src/`, one `.S` per kernel on shared
round and frame macros (`.inc`). The header of each file explains its design.

| Platform | Kernels | ns per 64-byte chunk |
|---|---|---|
| x86-64 AVX-512 (F, VL, BW) + BMI2 | `avx512_x9d`, `avx512_x8d`, `avx512vl_x4d`: the D-form rounds, all 25 lanes in registers and 35 instead of 60 vpternlogq per round, for cores that run a ternlog on fresh operands at half rate or count macro-ops (Zen 4: x9d 43 ns, 1.17x avx512_x9; Zen 5: x8d 21 ns, 1.19x avx512_x8); `avx512_x9` (avx512_x8 plus one node in the integer registers), `avx512_x8` (Ice Lake: two 512-bit ports count ALU ops), `avx512vl_x4` (cores with one 512-bit port); four-round loop bodies | 21 (Zen 5), 43 (Zen 4), 42 (Ice Lake; hashtree avx512_x16: 18) |
| x86-64 AVX2 (hybrid) | `avx2_x10`, `avx2_x9`, `avx2_x6`, `avx2_x5`: the AVX2 batches plus one or two nodes hashed in the integer registers (rorx, andn) in the gaps of the vector rounds; picked where the integer ALUs are separate from the vector pipes (Zen 3: x10, Gracemont: x6) | 67 (Zen 3; hashtree avx2_x8: 78, shani: 42) |
| x86-64 AVX2 | `avx2_x8`, `avx2_x4`, `avx2_x2` (calls of 2 nodes from `avx2_x10`) | 81 (Zen 3, avx2_x8) |
| x86-64 | `x86_x1` (a single node in the integer registers; the single-node tail of every AVX-512 and AVX2 kernel) | 219 (Zen 3; hashtree shani: 44) |
| AArch64 FEAT_SHA3 | `sha3_x3` (Neoverse), `sha3_x3r` (Apple), `sha3_x2` | 122 (Neoverse N2), 66 (Apple M1) |
| AArch64 | `neon_x3` (Neoverse N1), `scalar_x1`, `neon_x2` | 216 (Neoverse N1; hashtree neon_x4: 257) |
| RISC-V 64 | `rvv_zvkb`, `rvv`, `zbb_x1`, `rv64_x1` | not measured on hardware |
| any | `generic` (portable C, lane-complemented rounds) | 220 (Zen 3), 350 (Neoverse N1) |

Every x86-64 assembly kernel requires BMI1 and BMI2 (`x86_x1` uses `andn`
and `rorx`; the AVX-512 and AVX2 kernels through their `x86_x1` tail and the
hybrids' scalar nodes), besides the vector extension of its row; every
AVX2 CPU has them, but a hypervisor can hide them, and then the portable C
runs (about 220 ns per chunk on Zen 3).

Every kernel can also be called directly (`keccaktree_keccak256_<kernel>`).
Calling a kernel on a CPU that does not support it is undefined behavior.

## Building

The only build dependency is a GCC or clang compatible compiler and assembler.

```shell
make          # build/lib/libkeccaktree.a, build/test, build/bench
make test && ./build/test
make bench && ./build/bench
make bench HASHTREE=1 HASHTREE_DIR=/path/to/hashtree   # also bench hashtree (built in build/)
```

Cross compile with `CC`, e.g. `CC=aarch64-linux-gnu-gcc make` or
`CC=x86_64-w64-mingw32-gcc make test`.

## Bindings

Prebuilt static libraries for linux amd64/arm64/riscv64, darwin arm64 and
windows amd64 are in [`lib/`](lib/README.md). CI builds them on native
runners and attests their provenance. All bindings link these libraries.

- **Go** (`github.com/pk910/keccaktree`): `Hash(digests, chunks)` and
  `HashByteSlice`, with the same signatures and errors as hashtree-bindings,
  so switching is an import change. Other platforms and `CGO_ENABLED=0` use
  a pure-Go fallback (the unrolled generic round in Go). `bench/` compares it with hashtree-bindings.
- **Rust** (`Cargo.toml`, `src/lib.rs`): `keccaktree::hash(&mut out, &chunks, count)`
  with the hashtree-rs signature, `hash_in_place`, `hash_chunks`, `Backend`.
  `--features build-from-source` compiles `src/` instead of linking `lib/`.
- **Nim** (`keccaktree_abi.nimble`): `import keccaktree_abi`, like hashtree's
  `hashtree_abi`. `-d:keccaktreeFromSource` compiles `src/`.
- **Java** (`java/`, JNI, Java 11+): `Keccaktree.hash(out, in)`, with offsets,
  in-place and direct `ByteBuffer` variants. `java/build-native.sh` builds
  the JNI library from `lib/`.

## Contributing

CI tests pull requests against the libraries committed in `lib/`, so a pull
request that changes `src/` must commit rebuilt libraries. Run
`.github/scripts/build-pr-libs.sh` to cross-compile all of them with zig.
These are temporary: after the merge, CI rebuilds them on main with native
toolchains and attests them.

`.github/workflows/bench.yml` runs `build/bench` on GitHub's x86-64, Neoverse
N2 and Apple M1 runners. Start it by hand or push to a `bench/**` branch.
