# Agent `diff`: differential instruction tests of the models and the translator

Branch `all-diff` (worktree `src/wt-diff`), remote `/root/kt-diff` (repo copy `/root/kt-diff/repo`, kernel
objects `/root/kt-diff/kobj` assembled from `src/*.S` = upstream `origin/main` sources; their translation
is byte-identical to the committed `Program.lean` files except for the ARM fix below).

## Method (lean/difftest/README.md)
* Snippets: every distinct non-control instruction of the 24 kernels (x86 4.6k, AArch64 8.6k, RISC-V ~0.9k
  distinct texts; rip/literal/`.LRC` constants redirected into test constants) + random instances of every
  modelled form (templates: all registers incl. zmm16-31/k1-7, widths, immediates, memory operands,
  broadcasts, masks, write-back addressing, misaligned addresses) + control templates (flag setter + jcc,
  jcc to another function, jmp, call/ret, b.cond/cbz, RISC-V branches/j).
* Hardware: x86 natively (AVX2 host), EVEX forms under Intel SDE 9.48 `-spr`, AArch64 under
  qemu-aarch64 10.0 `-cpu max`, RISC-V under qemu-riscv64 `rv64,v,zbb,zvkb` with VLEN 128/256/512.
  A trampoline loads the full state (GPRs, vectors, masks, flags, vl), jumps to the snippet, captures the
  state at `kt_back`; memory regions are 32 KiB buffers with deterministic contents.
* Model: the snippet object goes through `objdump -d -r` → `asm2lean.py` (unchanged translator path) →
  `Tools/DiffCases/*.lean` → `difftool` (Lean, compiled) runs `X86/Arm/Riscv.run` on the same states.
* Compare (`compare.py`): GPRs, flags the model claims (x86 ZF/CF except after ops whose flags it does not
  model; ARM NZCV), vector lanes, masks, vl, every changed memory word; pointers modulo the region
  encoding.  States where the model reports `err` are counted but not compared.

## Findings

Severity: **B** = bug that affects kernel runs, **G** = model/translator imprecision outside the kernels'
use, now rejected by a translator guard (no kernel changed), **D** = documented domain assumption.

| # | ISA | what | status |
|---|---|---|---|
| M1 **B** | AArch64 | translator: post-indexed `ldp`/`stp`/`ldr`/`str` (`[sp], #N`) lost the base write-back (the comma split cut `#N` off). Kernels: the epilogue `ldp x29, x30, [sp], #N` (scalar_x1, sha3_x3, sha3_x3r, neon_x3) and `ldp d8, d9, [sp], #112` (neon_x2, sha3_x2): the model's `sp` after the epilogue was off by N — the state at `ret` **and the hand-over state of the tail calls** sha3_x3/neon_x3 → scalar_x1, sha3_x3r → sha3_x2. Digests unaffected (epilogue after the last store). | **fixed** (asm2lean), the 6 `Program.lean` regenerated (one instruction each). **The ARM proofs whose slices contain the epilogue (final slice / exit and hand-over segments) must be regenerated.** |
| M2 G | AArch64 | model: `ldr d` / `ldp d` keep lane 1, the CPU zeroes bits 64..127 | guard `check_dload`: after a d-load no vector instruction / q,d store before ret/tail call (kernels: only the d8-d15 restore in the epilogue) |
| M3 G | x86 | model: `vzeroupper` is a no-op, the CPU zeroes bits 128.. of ymm/zmm0-15 | guard `check_vzeroupper`: no vector instruction after it before ret/tail call (all 13 uses are in epilogues); vector registers are unconstrained in every `Entry` |
| M4 G | x86 | model: `kmovw k, [m]` with byte offset 7 reads only 8 bits | guard: rip-relative only, offset mod 8 ≤ 6 (kernels: 4 uses, offset ≡ 0) |
| M5 D | x86 | model: aligned moves (`vmovdqa*`) only need 8-byte alignment; the CPU faults below 32/64 | `alignaudit` (all x86 kernels, counts 0..64+2N): every executed aligned move addresses the stack frame; SDE run of upstream test.c with offsets 1..7 never aborts. Proposed model change in `notes/unaligned.md`. |
| M6 G | x86 | model: `cmp`/`sub` flags compare signed offsets; differ from the CPU's unsigned compare for negative immediates | guard: negative immediates rejected (kernels: none) |
| M7 G/D | x86 | model: `sub` on a pointer leaves the flags unchanged, the CPU sets them | guard: `sub` as a flag source only on rdx (the count; a number in every proved run: `Entry` fixes rdx = count, the paths inventory shows rdx only spilled/filled) |
| M8 G | x86 | translator: 32-bit forms (`dec ecx`, `cmp eax, imm`, `test eax, eax`, `mov r32, imm`, `xor r32, r32`) become 64-bit operations; other 32-bit forms (e.g. `mov eax, ebx`, `add eax, 1`) were silently translated as 64-bit | guard `check_r32`: only these forms; reads need the upper half zero (must-analysis over the CFG incl. call/ret), `dec r32` needs a non-zero input (taken `jne` after `dec`/`test`) |
| M9 G | RISC-V | model: `vsll.vx`/`vsrl.vx`/`vror.vx` with a count ≥ 64 give 0, the CPU uses the low 6 bits | guard `check_shift_counts`: the count register holds a `li` constant < 64 on every path (kernels: `li t4, k`, k ≤ 63). Model fix suggested: `n.toNat % 64` |
| M10 G | RISC-V | translator: `auipc rd, %pcrel_hi(.LRC+o)` is modelled as the full address; the CPU adds the low part in the next instruction | guard: the `%pcrel_lo` `addi rd, rd` (shown as `mv rd, rd`) or `ld rd, 0(rd)` must follow immediately (kernels: rv64/zbb use `ld`, rvv/zvkb the `la` pair) |
| M11 D | RISC-V | `vsetvli`: the model sets `vl = min(avl, VLMAX)`; RVV 1.0 lets an implementation choose any `vl` in `[ceil(avl/2), VLMAX]` when `VLMAX < avl < 2·VLMAX` (qemu and the known cores choose `min`) | documented: the RVV proofs cover implementations with `vl = min(avl, VLMAX)` |
| M12 D | all | words whose top byte is non-zero are decoded by `wordGpr` as pointers of region `r % 8` (a multiple of 8 decodes as the number of its low 56 bits): `add/sub/dec/cmp/test/bt/decm` and ARM/RISC-V address arithmetic on such words differ from the CPU | domain: counts < 2^54 (`Entry`), data words are never decoded (symbolic data lanes have no address: the model fails) |
| M13 D | all | data operations on pointer words compute on the model's encoding `(region << 56) + off`, not on the address | domain, checked: none of the 94k generated output facts (`theorem out…` in every `Gen*/Slice*.lean` of `/root/keccaktree` and `/root/kt-loop`) contains a `.ptr` leaf — the digests are functions of the input variables and data constants only |
| M14 D | x86 | `rep movsb` copies word lists (memmove); the CPU copies bytes forward (differs for overlapping ranges in one region) | domain: the kernels copy input → stack |
| M15 D | x86 | kernel objects also contain the threshold setters (`mov [rip+.data], rdi`); the model refuses stores to the constants (err) | not kernel code |

Test-harness lessons: objdump keeps the first object's RISC-V ISA subset for the following files (`.insn`
for vector instructions) — disassemble one object per call (the translator already does); the RISC-V
harness must not use gp-relative C code (`-mno-relax`), the snippets clobber gp.

## Results (final run `/root/kt-diff/x5`, seed 15, 4 states per kernel instruction, 60 instances per template form)

| set | runs on | snippets | states | agree | model err (not compared) | mismatch | mismatching forms |
|---|---|---|---|---|---|---|---|
| x86 VEX + scalar + control | native (AVX2) | ~6.9k | 16802 | 15964 | 607 | 158 (+73 aligned-move faults) | vzeroupper (152, M3), sub+jcc on a pointer rdx (3, M7), add [m] on a pointer with a large immediate (3, M12) |
| x86 EVEX (AVX-512) | SDE -spr | ~3.7k | 10200 | 10175 | 25 | 0 | — |
| AArch64 | qemu -cpu max | ~12k | 36820 | 36628 | 84 | 108 | ldr d / ldp d lane 1 (M2) |
| RISC-V VLEN 128 | qemu rv64,v,zbb,zvkb | ~2.3k | 5908 | 5868 | 40 | 0 | — |
| RISC-V VLEN 256 | " | ~2.3k | 5908 | 5866 | 42 | 0 | — |
| RISC-V VLEN 512 | " | ~2.3k | 5908 | 5856 | 52 | 0 | — |

Every mismatch left is one of the guarded (M2, M3) or domain (M7, M12) cases; the first runs also found
M1 (fixed), M4, M6, M8, M9, M10 (guarded) and test-harness artifacts (pointer values as data, `.data`
stores of the setter functions leaking into later cases, objdump ISA stickiness).
Constructor coverage (states that agree): x86 60/62 (`vzeroupper`: guarded; `tailcall`: the terminator of
every snippet), AArch64 33/36 (`tailcall` terminator of every snippet; `ret`, local `b` not exercised
separately), RISC-V 22/24 (`nop`, `unsupported`).  `model err` states are the model refusing (misaligned
addresses, pointer/region mismatches, non-whole-qword shuffles, ...) — the kernel proofs show `err = false`.

Translator guards: `lean/difftest/translator_guards.sh` (22 negative/positive cases, all pass); all 24 kernel
objects translate under the guards to exactly the committed `Program.lean` files (after the M1 fix).

Upstream test-suite on all backends (count 0..300, byte offsets 1..7, in place): see notes/unaligned.md §1
(all OK natively / SDE / qemu-aarch64 / qemu-riscv64 VLEN 128,256,512).

## Commands
```
# remote, /root/kt-diff: kernel objects in kobj/, repo copy in repo/ (rsync of lean/)
bash repo/lean/difftest/run_all.sh /root/kt-diff/x5 15 4 60     # ~20 min; reports in x5/<set>/report.txt, mismatches.txt
bash repo/lean/difftest/translator_guards.sh
bash repo/lean/difftest/run_audit.sh                              # aligned-move audit (alignaudit)
```
