# Formal verification of the portable kernel (Lean 4)

A machine-checked proof that keccaktree's portable kernel —
`src/keccak256_generic.c` and its pure-Go twin `keccak256_1_generic.go` —
and all thirteen assembly kernels compute keccak256 as FIPS 202 defines it,
for every input.

```shell
cd lean && lake build        # ~15 s, Lean 4.35, no Mathlib
```

## What is proved

`Keccaktree/Proof.lean`, for every 64-byte node `input` and digest byte `j < 32`:

```lean
theorem node_spec (input : Nat → BitVec 8) (j : Fin 32) :
    (node input)[j] = Spec.keccak256 64 input j

theorem hash_spec (input : Nat → BitVec 8) (k : Nat) (j : Fin 32) :
    (hash input k)[j] = Spec.keccak256 64 (fun i => input (64 * k + i)) j
```

`node` is the body of the loop in `keccaktree_keccak256_generic` (lanes
0…7 loaded little-endian, `a[8] = 0x01`, `a[16] = 1 << 63`, `keccak_f1600`,
lanes 0…3 stored little-endian); `hash input k` is digest `k` of a batch.
`Spec.keccak256 len m` is the independent specification.  Along the way:

| theorem | statement |
|---|---|
| `theta_spec`, `rhoPi_spec`, `chi_spec`, `iota_spec` | each step of the C round body is the corresponding step function of FIPS 202 (θ, ρ then π, χ, ι) |
| `round_spec` | one iteration of the C round loop is `Rnd(A, r)`, for every `r` and state |
| `keccakF_spec` | `keccak_f1600` is Keccak-f[1600] (24 rounds) |
| `init_spec` | the state the C code builds is the sponge state after absorbing the padded 64-byte block |
| `Spec.rhoOffset_eq`, `Spec.RC_eq` | the hard-coded ρ offsets and round constants are the ones FIPS 202 *derives* (triangular numbers along the (x,y)↦(y,2x+3y) orbit; the `rc(t)` LFSR of Algorithm 5) |

## Files

| file | role |
|---|---|
| `Keccaktree/Spec.lean` | **Specification.** Keccak-f[1600] written as the lane formulas of FIPS 202 §3.2 (θ, ρ, π, χ, ι on `A[x][y]`), with ρ offsets and round constants derived from the standard's definitions, and the keccak256 sponge: `pad10*1` with domain byte `0x01` (Ethereum keccak256, not SHA3-256's `0x06`), rate 1088 (17 lanes), absorb, squeeze 32 bytes.  Any message length. |
| `Keccaktree/SpecVectors.lean` | The spec against an independent implementation (`golang.org/x/crypto/sha3` `NewLegacyKeccak256`): 12 known-answer vectors (`vectors/oracle.txt`), including messages that span 1, 2 and 3 blocks (the multi-block vectors caught a bug in a first draft of `absorb` that xored into the capacity lanes). |
| `Keccaktree/Generic.lean` | **Model.** `keccak256_generic.c` as a Lean program: `uint64_t a[25]` is `Vector (BitVec 64) 25`, the `RC`/`RHO`/`PI` tables are copied verbatim (`check_tables.py` diffs them against the C and Go sources), θ and χ are per-lane `Vector.ofFn` (independent iterations), ρ+π is the in-place walk along π's 24-cycle with the carried temporary exactly as in the C (`rhoPiLoop`), `ld64`/`st64` are the byte loops. |
| `Keccaktree/GenericVectors.lean` | The model executed on the oracle vectors (sanity check that it is the same program as the C). |
| `Keccaktree/Proof.lean` | **Proof.** |

## How the proof works

* **One step at a time.** θ, χ and ι are unfolded to 25 lane equations
  (`State.ext25`) and decided by `bv_decide` (bit-blasting + SAT, with the
  LRAT certificate checked by Lean's verified checker), or closed by `simp`
  alone when both sides coincide syntactically (χ, ι).
* **ρ/π by reflection.**  Unrolling the 24 in-place updates symbolically with
  `simp` is exponential (the carried temporary duplicates the update chain),
  so the loop is run on *symbolic lanes* (`RhoPi.E`): `loop_eval` proves once,
  by induction on the iteration count, that the C loop on evaluated lanes
  equals the evaluation of the symbolic loop; the kernel then *computes* the
  symbolic result of 24 iterations (`loopE_0 … loopE_24`, each by `rfl`),
  which is exactly ρ followed by π.  This is the one part of the C code that
  is not obviously correct by inspection, and the proof pins down the
  permutation it implements.
* **Rounds by induction** (`rounds_spec`), the round constant tables by 24
  `rfl`s, the initial state and the byte stores by `bv_decide` and by
  `extractLsb'`'s definition.

## Trust base

* The Lean 4 kernel, plus `propext`, `Classical.choice`, `Quot.sound`.
* `bv_decide` (in `theta_spec` and `init_spec`): the SAT solver's LRAT proof
  is checked by a verified checker run as compiled code (`Lean.ofReduceBool`;
  shown by `#print axioms` as `…_native.bv_decide.ax_*`).  Everything else,
  including `rhoPi_spec` and the FIPS derivations of the tables, is checked
  by the kernel alone.
* The model is a transliteration of the C.  It is kept honest by executing
  it on the same vectors as the C test suite and by `check_tables.py`; the
  Go file is line-for-line the same algorithm.
* `native_decide` is used only for the executable test vectors, never in
  the proof.

## The assembly kernels

The thirteen hand-written kernels (`src/keccak256_*.S`: x86-64 AVX2/AVX-512,
AArch64 NEON/SHA3/scalar, RISC-V scalar/Zbb/RVV) are verified against the
same specification at the machine-code level.  The object code is the thing
proved about: `asm2lean.py` disassembles the assembled `.o` files (`objdump
-d -r`) into Lean programs (`Keccaktree/Kernels/<K>/Program.lean`), which are
executed by instruction-set models and shown to compute keccak256.

```shell
lake build kttool                   # the proof-generation tool (symbolic executor, matcher)
./gen_all.sh                        # generate Keccaktree/Kernels/<K>/Gen/*.lean (minutes)
./build_bounded.sh ScalarX1 6       # check one kernel's proofs with ≤ 6 lean processes (5–40 min, 2–15 GB each)
```

### What is proved

For every kernel `K`, `Keccaktree/Kernels/K/Gen/Final.lean` ends with

```lean
theorem kernel_keccak256 (input : Int → BitVec 64) :
    (finalState input).halted = true ∧ (finalState input).err = false ∧
    ∀ n w i : Nat, n < count → w < 4 → i < 8 →
      ((finalState input).mem rOutput (Int.ofNat (4 * n + w))).extractLsb' (8 * i) 8 =
        Spec.keccak256 64 (nodeBytes (nodeWords input n)) (8 * w + i)
```

`finalState input` runs the kernel's machine code from its entry point
(`keccaktree_keccak256_<K>(out, in, count)` with `count` = the nodes of one
batch: 4 or 8 for x86, 1/2/3 for AArch64, 1 or `VLEN/64` for RISC-V) on an
arbitrary input region `input` until its final `ret`; the theorem says the
run never hits an unmodelled situation (`err = false`), halts, and every byte
of every output digest is `Spec.keccak256` of the corresponding 64 input
bytes.  `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`
and `bv_decide`'s checked certificates.

### How

* **Machine models** (`Keccaktree/Asm/X86.lean`, `Arm.lean`, `Riscv.lean`):
  the instruction subsets the kernels use, on one shared state (vector
  registers of 8 lanes, general registers, flags, AVX-512 masks, RVV `vl`,
  memory as regions of 64-bit words: input, output, stack, constants).
  Pointers are tagged addresses; anything the model does not cover
  (unaligned byte-copy paths, unsupported configurations) makes `exec` fail,
  and the theorems assert it never does.  The models are polymorphic in the
  lane type (`LaneOps`), so the same `exec` is the concrete interpreter — run
  on the C test vectors for every kernel (`Kernels/*/Test.lean`) — and the
  symbolic executor on expression trees `E`.
* **Slices and cuts.**  A batch is cut at the 23 round boundaries (found by
  `kttool`, which runs the kernel on two random inputs and recognises which
  spec quantity — lane, θ-parity, θ-output, rotated, or a round constant
  held for the next round — each register and stack word holds).  Each slice is run once symbolically from a cut state whose
  data locations are fresh variables (`cutOf`); the result is checked by the
  kernel (`decide +kernel`), and one `bv_decide` lemma per distinct
  expression shape (shared by all nodes) proves that the slice's outputs are
  the next round's quantities of the inputs' quantities (`Invs.lean` holds
  the invariant at every cut; `RoundLanes.lean` the spec round as 25 lane
  formulas, by `rfl`).
* **Composition** (`Trace.lean`, `Compose.lean`, `Final.lean`): `exec`
  commutes with lane homomorphisms (`exec_map`, one lemma per instruction),
  so the concrete run of a slice is the evaluation of the symbolic one
  (`execTrace_cut`); `pathOk` (kernel-checked) shows the fetch–execute loop
  follows the recorded instruction path; `run_batch` chains the 24 slices,
  `entry_cut` connects the kernel's entry state, and `Node.lean` connects the
  sponge states to `Spec.keccak256` on bytes.

### Limits

* One batch per call: `count` is the kernel's batch size.  Other counts
  (the loop over several batches and the tail-size hand-overs
  `avx512_x8 → avx512vl_x4`, `sha3_x3 → scalar_x1/sha3_x2`, …) are executed by
  the models but not yet proved; the composition needs a relocation lemma
  for the pointer arithmetic between batches.
* RVV kernels are proved for `VLEN ∈ {128, 256, 512}` (`vlmax = 2, 4, 8`
  lanes); vector tail lanes are modelled as undisturbed.
* Buffers are assumed 8-byte aligned (the kernels' byte-copy fallbacks are
  not modelled).

## Trust base (assembly)

As above, plus: the disassembly (`objdump`) and the translation of its
text to the instruction models (`asm2lean.py`, 1:1 per mnemonic), and the
instruction semantics themselves (checked against the C test vectors, with
tail hand-overs, through the executable interpreter).  The generated proofs
are regenerable from the `.o` files; nothing in them is trusted.
