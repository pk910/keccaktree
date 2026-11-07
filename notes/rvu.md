# Agent `rvu`: RISC-V with misaligned buffers (byte copies / bounce paths) and the M9 fix

Branch `all-rvu` (worktree `src/wt-rvu`, off lean-verification 6774b63), remote workspace `/root/kt-rvu`
(its `.lake` is the one of `/root/kt-rv`, **moved** there: the disk was full (0 bytes free, 301 GB) and a
copy of 85 GB impossible; the RISC-V/x86_x1 build outputs in it were stale anyway (core files changed) and
were deleted, freeing ~80 GB).  Design: `notes/rv_unaligned_vlen.md` (agent `rv`); this file: what was
done, how, and what is open.

## Remote commands
* `/root/kt-rvu-run.sh <name> <MemoryMax> <cmd…>`: runs `<cmd>` in `/root/kt-rvu/lean` as the transient
  unit `kt-rvu-<name>` (systemd, detached from ssh, memory-capped, `OOMPolicy=continue`), log
  `/root/kt-rvu-logs/<name>.log` ending in `EXIT <rc>`.
* sync: `rsync -a --exclude .lake --exclude .git --exclude 'Gen*/' --exclude Tools/DiffCases ./ root@…:/root/kt-rvu/`
* difftests (RISC-V only): `KOBJ=/root/kt-rvu/kobj bash difftest/run_rv.sh <workdir> <seed> [ns] [nt]`
  (objects: `riscv64-linux-gnu-gcc -g -fpic -c src/keccak256_<k>.S`).

## Milestone 1: model, translator, differential tests (done)
Core changes (all RISC-V-only; x86/ARM untouched):
* `Asm/Riscv.lean`: new instructions `lbu`, `sb`, `vsetvlie8 d a lmul` (`vsetvli d, a, e8, m<lmul>`: `vl` in
  bytes; fails if `avl > 8·vlmax·lmul`, so no vl choice is involved), `vle8`, `vse8` (word `j` of the
  transfer ↔ register `d + j / vlmax`, lane `j % vlmax`; `vl % 8 = 0` required).  Byte addresses are
  region-relative: byte `o % 8` of word `o / 8` (`wordOf`, `byteOf`); `lbu` = shift+mask of the word,
  `sb` = masked insert (`insByte`, read-modify-write of the word); `vle8`/`vse8` at a misaligned address
  assemble each word from / split it into the two words it straddles (`joinWords`, `splitWords`,
  `loadBytes`, `storeBytes`, `setGroup`, `groupWord`, `setLanes`).  All built from `LaneOps`, so the
  homomorphism / relocation / footprint proofs are structural.
* **M9 fixed**: `vsh .sll/.srl a n = shl/shr a (n % 64)` (hardware: low 6 bits).
* `RiscvHom` (`exec_map`, `err_exec`), `RiscvReloc` (`decodes` += base of the byte accesses, `exec_reloc`;
  `wordOf_reloc`, `byteOf_reloc`: relocations move by multiples of 8 bytes), `RiscvFoot` (`writes`:
  `sb` its word, `vse8` its `vl/8` (+1 if misaligned) words; `exec_frame`), `RiscvEntryCtl` (`isVec` +=
  `vle8/vse8` (read `vl`), `ctlAfter vsetvlie8` = `vl` defined; `exec_ovr`, `exec_pc`),
  `RiscvSteps` (`usesVlmax` += the three byte-vector instructions; new `Instr.isVset` = only the e64
  `vsetvli`, where the hardware may choose `vl`), `RiscvChoice` (`execCh_map`/`execCh_min` by `isVset`;
  new `vlFor_not_isVset`, `execCh_not_isVset`; old statements unchanged).
* `Kernels/RvVl.lean`: the scalar kernels' `vl`-dirty intervals are now the whole program
  (`[(1, 5430)]`, `[(1, 3499)]`): the byte loops fall through instead of stopping at `unsupported`.
* Translator `asm2lean.py`: `lbu`, `sb`, `vsetvli …, e8, m1/2/4/8`, `vle8.v`, `vse8.v` (unmasked);
  `vsetvli` with `rs1 = x0` is `unsupported` (VLMAX / keep-vl semantics, not modelled; unused);
  new guard `check_vtype` (forward may-analysis of the last `vsetvli`: no e64 vector instruction under
  an e8 setting, `vle8/vse8` only under one) — the model has no `vtype`.  The 4 `Program.lean`
  regenerated: only the 14 former `unsupported` lines change.
* `Tools`: `riscvStoreCells` += `sb`, `vse8`; `riscvMisalign` and `KT_MIS=mi,mo` (kttool runs with the
  buffers at byte offsets `mi`/`mo`, the message shifted accordingly).
* `gen_plan_proof.py`: `INV0`/`INVK` (the invariant locations at a segment's ends: `input` (default) /
  `out` (default) / `regs` / `mem<r>` / `all`; round-constant look-alikes dropped there).

Differential tests (`difftest/rvgen.py`: templates for `lbu`/`sb` at any byte offset, e8 `vle8`/`vse8`
at every LMUL and vl, load+store pairs between misaligned buffers, the two kernel bounce sequences;
shift counts ≥ 64 for `vsll/vsrl/vror.vx`), qemu-riscv64 `rv64,v,zbb,zvkb` VLEN 128/256/512, two seeds:
0 mismatching forms (dt1: 5386/5376/5375 states compared, dt2: 5377/5381/5386; ~130 `lbu`, ~130 `sb`,
~470 `vle8`, ~470 `vse8`, ~110 per bounce sequence per VLEN, 59 shifts by counts ≥ 64 at VLEN 128).
