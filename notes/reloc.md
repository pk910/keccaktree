# reloc — pointer-tagged lanes and the relocation lemma

Branch `reloc` (worktree `src/wt-reloc`), remote build dir `/root/kt-reloc`.

## Status
- Pointer-tagged core: DONE (Machine/Lemmas/Hom/ArmHom/RiscvHom/Compose/Tools; whole library builds).
- `Reloc.lean` (x86) + `ArmReloc.lean` + `RiscvReloc.lean`: DONE, no `sorry`.
- Merged `lean-verification` (e713c7d, specQuantity split) into `reloc`: f45f2f7.
- End-to-end validation (X86X1, ScalarX1 regenerated with `.ptr` leaves): see below.

## Model changes (semantics)
- `LaneOps` gains `ptr : Addr → α` and `asAddr : α → Option Addr`.
  BitVec: `ptr = gprWord`, `asAddr w = some (wordGpr w)` (exactly the old decoding).
  `E`: new leaf `.ptr a`; `asAddr = E.addr` (closed number word ↦ `Addr.num`, else `E.addrP`:
  pointer leaf, pointer ± closed constant via `addrPlus`, `(ptrs) & m` with `m ⊆ 7` via `E.low3`);
  `asConst = E.closed` (`.ptr a` is closed only for region 0 = numbers).
- `gprWord a = (region <<< 56) + ofInt off` (was `ofNat (region*2^56 + off.toNat)`; same for wf addrs).
  `Addr.wf : 0 ≤ off < 2^55`.
- All three models decode addresses/counts with `asAddr` (`gx`, `memAddr?`, `cmpm/cmprm/decm/ret` loaded
  words, RISC-V `br` compares offsets of the same region) and write them with `ptr` (`setX`, `call` return
  address, `decm`). `asConst` only for data constants (RC, masks, shift counts, vsetvli AVL, `bt`).
- Restricted to their real uses (fail otherwise; harnesses unaffected): x86 `andi` only on the stack,
  `dec`/`decm` only on numbers (counters); RISC-V `lea` (auipc) only into the constants.
- `cutVar`: a control word whose value is a faithfully encoded pointer (`wordGpr w` has region ≠ 0 and
  re-encodes to `w`) becomes `.ptr (wordGpr w)`, other control words `.const w`.
- `IsHom` gains `ptr`, `asAddr`; new `IsLaneHom` (lane ops only) with `IsHom.lane`; the lane-only helper
  lemmas of `Hom.lean` (`getD_map`, `lane128_map`, `allSome_map`, `shufb128_map'`, …) take `IsLaneHom`.

## Interface (Keccaktree/Asm/Reloc.lean, ArmReloc.lean, RiscvReloc.lean)
```lean
structure Reloc where δ : Region → Int
def Reloc.ok (ρ) : Prop := ρ.δ 0 = 0 ∧ ρ.δ rStack = 0 ∧ ρ.δ rRodata = 0 ∧ ∀ r, 0 ≤ ρ.δ r ∧ 8 ∣ ρ.δ r
def Reloc.addr (ρ) (a : Addr) : Addr := ⟨a.region, a.off + ρ.δ a.region⟩
def Reloc.wshift (ρ) (r) : Int := ρ.δ r / 8
def Reloc.var (ρ) (i : Nat) : Nat   -- memVar r q ↦ memVar r (q + wshift r); i < 288 fixed
def E.reloc (ρ) : E → E             -- .var i ↦ .var (ρ.var i), .ptr a ↦ .ptr (ρ.addr a)
def X86.relocState (ρ) (s : State E) : State E   -- lanes reloc'd, mem r q := reloc (s.mem r (q - wshift r))
def E.addrs (e : E) : List Addr     -- addresses decoded inside e
def E.relocOk (ρ) (e) : Prop := ∀ p ∈ e.addrs, (ρ.addr p).wf
def E.addrsBelow (B : Int) (e : E) : Bool          -- decidable
def Reloc.within (ρ) (B : Int) : Prop := ∀ r, ρ.δ r + B ≤ 2^55
theorem E.relocOk_of_below : ρ.ok → ρ.within B → e.addrsBelow B = true → E.relocOk ρ e

-- per ISA: decodes (the lane values a step decodes as addresses) and
theorem X86.exec_reloc (ρ) (hρ : ρ.ok) (rodata) (i) (st : State E)
    (hne : (exec rodata i st).err = false) (hok : ∀ e ∈ X86.decodes rodata i st, E.relocOk ρ e) :
    exec rodata i (relocState ρ st) = relocState ρ (exec rodata i st)
theorem Arm.exec_reloc   -- same shape, Arm.decodes
theorem Riscv.exec_reloc (ρ) (hρ) (vlmax) …  -- same shape, Riscv.decodes

structure Isa.Relocatable (isa : Isa) where
  decodes : Array (BitVec 64) → isa.Instr → State E → List E
  exec_reloc : ∀ ρ, ρ.ok → ∀ rodata i st, (isa.exec rodata i st).err = false →
    (∀ e ∈ decodes rodata i st, E.relocOk ρ e) →
    isa.exec rodata i (relocState ρ st) = relocState ρ (isa.exec rodata i st)
def X86.isaReloc : X86.isa.Relocatable;  def Arm.isaReloc : Arm.isa.Relocatable
def Riscv.isaReloc (vlmax) : (Riscv.isa vlmax).Relocatable
def Isa.Relocatable.traceDecodes (R) (rodata) : List isa.Instr → State E → List E
theorem Isa.Relocatable.execTrace_reloc (R) (ρ) (hρ) (rodata) (l) (st)
    (hne : (isa.execTrace rodata l st).err = false) (hok : ∀ e ∈ R.traceDecodes rodata l st, E.relocOk ρ e) :
    isa.execTrace rodata l (relocState ρ st) = relocState ρ (isa.execTrace rodata l st)

-- evaluation
def E.evalP (pt : Addr → BitVec 64) (env) : E → BitVec 64
theorem E.eval_eq_evalP : E.eval env e = E.evalP gprWord env e
theorem E.eval_reloc : E.eval env (e.reloc ρ) = E.evalP (fun a => gprWord (ρ.addr a)) (fun i => env (ρ.var i)) e
def E.noPtr : E → Bool
theorem E.eval_reloc_noPtr (h : e.noPtr = true) : E.eval env (e.reloc ρ) = E.eval (fun i => env (ρ.var i)) e

-- cuts and the concrete transfer
theorem X86.relocState_cutOf (ρ) (ctl) (S0 Sk : State (BitVec 64))
    (hctl : ∀ i ∈ ctl, cutVar ctl Sk i = E.reloc ρ (cutVar ctl S0 i))
    (hmem : ∀ i ∈ ctl, 288 ≤ i → ρ.wshift (memVarRegion i) = 0)
    (hc : Sk.g = S0.g ∧ Sk.k = S0.k ∧ Sk.zf = S0.zf ∧ Sk.cf = S0.cf ∧ Sk.nf = S0.nf ∧ Sk.vf = S0.vf ∧
          Sk.vl = S0.vl ∧ Sk.pc = S0.pc ∧ Sk.depth = S0.depth) :
    relocState ρ (cutOf ctl S0) = cutOf ctl Sk
theorem Isa.Relocatable.execTrace_reloc_concrete (R) (ρ) (hρ) (rodata) (slice) (ctl) (S0 Sk)
    (hcut : relocState ρ (cutOf ctl S0) = cutOf ctl Sk)
    (hs : Sk.err = false ∧ Sk.halted = false ∧ Sk.tail = none)
    (hne : (isa.execTrace rodata slice (cutOf ctl S0)).err = false)
    (hok : ∀ e ∈ R.traceDecodes rodata slice (cutOf ctl S0), E.relocOk ρ e) :
    isa.execTrace rodata slice Sk = mapState (E.eval (envOf Sk)) (relocState ρ (isa.execTrace rodata slice (cutOf ctl S0)))
```

### How the composition uses it
1. Prove the batch body once at iteration 0 from `cut0 := cutOf ctl S0` (existing generator).
2. Kernel-check `(R.traceDecodes rodata body cut0).all (E.addrsBelow B) = true` (closed, cheap: only the
   base/count registers' small trees) with e.g. `B = 2^54`; then any `ρ` with `ρ.within B` satisfies `hok`
   via `E.relocOk_of_below`.
3. For iteration k: `ρ_k.δ rInput = 64·NODES·k`, `ρ_k.δ rOutput = 32·NODES·k`, others 0;
   `relocState_cutOf` (control pointers moved, control counts equal, control cells on the stack only).
   The count register must not be a control word of the body (only of the loop test).
4. `execTrace_reloc_concrete` + `E.eval_reloc_noPtr` give the concrete digests of iteration k from the
   symbolic digests of iteration 0, read at shifted memory variables (`ρ.var (memVar rInput q) =
   memVar rInput (q + 8·NODES·k)`).

## Commands
```bash
cd ~/projects/keccaktree-lean-verify/src/wt-reloc
sshpass -p ClaudePass123 rsync -az -e ssh --exclude .lake --exclude .git --exclude '*/Gen/' --exclude 'Gen/' ./ root@2.28.133.253:/root/kt-reloc/
# remote: cd /root/kt-reloc/lean; lake build Keccaktree kttool
#         BATCH=1 ./gen_all.sh x86_x1 scalar_x1; ./build_bounded.sh X86X1 4; ./build_bounded.sh ScalarX1 4
```

## Open issues
- The generated proofs of every kernel must be regenerated on this core (trees now contain `.ptr` leaves;
  `entry_cut` etc. unchanged in shape).
- `traceDecodes` along a body is not yet emitted by the generator (step 2 above) — composition agent's job.
