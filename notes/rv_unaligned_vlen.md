# RISC-V: misaligned buffers and VLEN ≥ 1024 — analysis, decisions, plan

Agent `rv`, 2026-11-07 (after the RISC-V every-count proofs, all-rv 8231a14, merged as f9fddac).
Task from main: (1) prove the RISC-V bounce paths (misaligned input/output) and fold in the M9 shift fix;
(2) determine what the dispatcher does at VLEN ≥ 1024 and, if feasible, make the lane count a parameter.

## (2) VLEN ≥ 1024: what the library does, and what the model can say

**Dispatcher** (`src/keccaktree.c`, upstream = verified sources):
* `v = (hwprobe IMA_EXT_0 has V) && vlenb >= 16` — VLEN ≥ 128, **no upper bound**.
* Candidates: `rv64_x1`, `zbb_x1` (Zbb), `rvv` (V), `rvv_zvkb` (V + Zvkb); `keccaktree_calibrate` times them
  and keeps the fastest — so on a VLEN ≥ 1024 machine `rvv`/`rvv_zvkb` is selected whenever it is fastest
  (in practice: always, it hashes VLEN/64 nodes per batch).
* The kernels are vector-length agnostic: `vsetvli t0, t3, e64, m1, ta, ma` with `t3 =` nodes left, so
  `vl = min(count, VLEN/64)` nodes per batch (RVV 1.0 legal choices between ⌈avl/2⌉ and VLMAX also covered
  by `RiscvChoice` for VLEN ≤ 512): 16 nodes per batch at VLEN 1024, up to 1024 nodes at VLEN 65536.
  LMUL = 1 throughout the aligned path.  The misaligned path caps the batch at `BOUNCE_NODES = 8` and moves
  the bytes with `vsetvli e8, m8` (64·vl ≤ VLEN bytes) and `e8, m4` (32·vl bytes).

**Model**: a vector register is `Vector α 8` (8 lanes of 64 bits = VLEN 512).  The width 8 is hard-wired in
22 core files: `State.v : Vector (Vector α 8) 32`, the cut-variable numbering (`regVar r l = 8r + l < 256`,
`gdVar = 256 + n`, `memVar = 288 + …`), `Riscv.setActive` (`Fin 8`), the x86 zmm (8 lanes) and AArch64 q/d
views, `Compose`/`Reloc`/`Iter`/`Hom`/`Footprint`, the kttool scanner, and every generated proof (literal
`Vector.replicate 8` states in every slice of every kernel of every ISA).

**Decision**: not feasible in this phase.  A lane-count parameter `State (L : Nat)` changes the type of every
state and the variable encoding used by all generated proofs (x86, ARM, RISC-V: ~2,000 slice files), i.e. a
full regeneration and rebuild of the whole project, plus RVV body variants for `vl = 1..L` (the symbolic
method proves one body per `vl` value: L = 16 means 16 more variants per kernel, each with up to 16 nodes —
cost grows ~ L² per VLEN).  A VLEN-generic proof needs a different argument (lane independence: every RVV
body instruction is lane-wise except `vlseg`/`vsseg`, whose lane `l` touches node `l` only — a "slicing"
theorem `run_{VLEN} = interleave of run_{512}` would transfer the VLEN-512 proofs; not attempted).

**Exact coverage statement** (also in `RvLib.lean`): RVV theorems for VLEN ∈ {128, 256, 512} (`lib2/4/8`,
`lib2ch/4ch/8ch`).  On VLEN ≥ 1024 hardware the dispatcher can select `rvv`/`rvv_zvkb`, which is **outside
the proved configurations**; the scalar kernels (`rv64_x1`, `zbb_x1`) are proved for every vlmax.
Possible library-side mitigation (upstream decision, not a proof): cap the RVV candidates at `vlenb <= 64`.

## (1) Misaligned buffers (bounce paths)

### Kernel code (from `src/keccak256_rv64.inc`, `keccak256_rvv.inc`)
* rv64_x1 / zbb_x1, per node: `ld t0, IN(sp); addi t1,t0,64; sd t1,IN(sp); andi t1,t0,7; beqz t1, 2f`;
  misaligned: `COPY_BYTES sp+BUF ← t0, 64` (`lbu; sb; addi; addi; addi; bnez` × 64 = 384 steps), `t0 = sp+BUF`;
  `LOAD_STATE t0`, 24 rounds; output: `andi t1, t0, 7; bnez` → misaligned: 4 `sd` to `BUF`, `COPY_BYTES out ← BUF, 32`.
* rvv / rvv_zvkb, per batch: `a7 = (a0|a1)&7`; if `a7 ≠ 0`: `vl ≤ 8`; input via `vsetvli zero, 64·vl, e8, m8;
  vle8.v v24,(a1); vse8.v v24,(sp); vsetvli zero, vl, e64, m1; vlseg8e64.v v0,(sp)`; output via
  `vsseg4e64.v v0,(sp); vsetvli zero, 32·vl, e8, m4; vle8.v v24,(sp); vse8.v v24,(a0)`.

### Model design (additive to `Riscv.lean`; all other ISAs untouched)
* **Misalignment as region-relative offset**: no new `State` field.  A buffer whose machine address is
  `≡ m (mod 8)` is modelled as the region pointer `⟨r, m + 64·off⟩` (input) / `⟨r, m' + 32·off⟩` (output); the
  message bytes start at region byte `m`.  `E.low3 (.ptr ⟨r, o⟩) = o mod 8` then gives the kernel's alignment
  test exactly (`a7 = (m | m') & 7`), the aligned path is the case `m = m' = 0` (today's proofs), and
  relocation by whole nodes (64/32 bytes) keeps `o mod 8`, so `Reloc`/`Iter` need no change.
* New instructions (replacing the `.unsupported` forms in the 4 programs):
  `lbu d, off(b)` = `(W[o/8] >>> 8·(o%8)) &&& 0xff`; `sb s, off(b)` = masked byte insert into `W[o/8]`
  (never into the constants); `vsetvlie8 a, lmul` (`vl := min(avl, 8·vlmax·lmul)` bytes; in the kernels
  `avl ≤ VLMAX` always, so this is the only legal choice); `vle8 d, (b)` / `vse8 s, (b)` with `vl % 8 = 0`:
  word `j` of the transfer ↔ register `d + j / vlmax`, lane `j % vlmax`; at a word-aligned address a word
  copy, at a misaligned one each word is assembled from / split into two memory words
  (`(W[q] >>> 8k) ||| (W[q+1] <<< (64-8k))`, masked inserts).  All with the existing `LaneOps`
  (`and/or/shl/shr/not/const`), so `exec_map`/`exec_reloc`/footprint proofs are structural; per new
  constructor: `RiscvHom`, `RiscvReloc` (`decodes` += base register), `RiscvFoot` (`sb`: 1 cell, `vse8`:
  `n` or `n+1` cells), `RiscvEntryCtl` (`vle8/vse8` read `vl`, `vsetvlie8` writes it; successors = next),
  `RiscvChoice` (not a `.vsetvli`: deterministic), translator `asm2lean.py` (lines 786/794).
* **M9**: `vsh .sll/.srl a n = shl/shr a (n % 64)` (hardware semantics).  Same values for `n < 64`; the
  generated trees are kernel-evaluated, so the proofs regenerate unchanged — but `Riscv.lean` changes, so
  every RISC-V slice must be rebuilt (fold into the same rebuild).

### Proof plan (per kernel; the existing pipeline)
* **Restructure the body into load / core / store segments** so the 24-round core is proved once for all
  alignment classes: cut after `LOAD_STATE` (state = absorbed lanes in registers, control words sp + spill
  cells) and before the digest stores.  Load segments: `aligned` (from input) and `misaligned` (from BUF);
  store segments: `aligned`/`misaligned`.  The byte copies (`COPY_BYTES`, `vle8/vse8`) are separate small
  segments per misalignment `m ∈ 1..7` (the shift amounts are constants of the symbolic run; `low3` is
  relocation-invariant), each with one `bv_decide` lemma per word: "stack word j = message word j" from the
  two region words it straddles.
* RVV: bounce bodies `GenM<w>` for `w = 1..min(8, VLMAX)` (the misaligned batch is capped at 8 nodes); the
  core rounds are the existing per-`w` bodies if the cut is placed after `vlseg8e64` (lanes in v0..v24) and
  before `vsseg4e64` — then only the load/store ends differ.
* **Statement**: `Entry` gains `m_in m_out < 8`; the message and the digest become byte-addressed
  (`DigestB m_out`: byte `m_out + 32n + j` of region 2 = byte `j` of keccak256 of node `n`, the node read
  from region-1 bytes `m_in + 64n + i`); `m_in = m_out = 0` gives back `LibX86.Digest`.  The library layer
  needs `EntryRv`/`Digest` variants with the misalignment (owned by `lib`; additive).
* **Cost** (current machine load ~120–160 on 32 cores): every RISC-V proof rebuilt (≈ the 8 h of this
  phase: rv64_x1 body 3 h, RVV 2–5 h per VLEN), plus the misaligned segments: scalar kernels ≈ 7 copy-in +
  7 copy-out segments (small), RVV `GenM<w>` load/store ends ×(≤ 8 per VLEN) per kernel.  Estimate:
  2–3 days of agent time and ~15–20 h of build time.

### Status
Nothing implemented yet for (1) (this document only).  (2) is answered above: documented as not covered.
