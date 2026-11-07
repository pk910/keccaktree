# Formal verification of the portable kernel (Lean 4)

A machine-checked proof that keccaktree's portable kernel —
`src/keccak256_generic.c` and its pure-Go twin `keccak256_1_generic.go` —
computes keccak256 as FIPS 202 defines it, for every input.

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

## Not covered

The assembly kernels (`src/keccak256_*.S`) are hand-written for each ISA
and are outside what this proof covers; they remain validated by the
differential tests in `src/test.c` and the Go test suite against the
portable kernel and against `x/crypto`.
