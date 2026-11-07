import Keccaktree.Asm.LibTable
import Keccaktree.Asm.Rodata
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The dispatcher `src/keccaktree.c`

A model of the runtime dispatch (source: upstream `src/keccaktree.c` at the proved
commit): `keccaktree_detect` reads the CPU's feature report and selects a kernel,
times the feature-qualified candidates (`keccaktree_calibrate`) and, on the AVX2
path, sets the two runtime thresholds; `keccaktree_init(NULL)` stores the result,
`keccaktree_hash(out, in, count)` calls it with the same arguments.

**Modelled**: the decision structure of `keccaktree_detect` for x86-64, AArch64 and
RISC-V (features as parameters), calibration as an oracle that returns one of
its candidates (the C loop returns an index in `[0, n)`), the threshold writes
(`keccaktree_avx2_small_tail`, `keccaktree_avx2_x10_mid_tail`, their `.data`
defaults 1 and 4).
**Trusted / out of the model**: the C compiler and the calling convention
(argument registers, `call` through `hash_ptr`), the CPU's feature report, the
calibration runs themselves (they hash a static scratch buffer in place,
`fns[i](buf, buf, n)`, results discarded; the kernel models assume disjoint
input/output regions), user `override` functions (called as given), and the
memory-model assumption for concurrent first calls (aligned 8-byte plain stores
and loads of `hash_ptr` and the thresholds are not torn).

**Proved**:
* `detectX86_sound`, `detectArm_sound`, `detectRv_sound`: the selected
  implementation is the portable C kernel or a kernel of the library table of that
  instruction set, and the CPU reports every feature the kernel *and every kernel it
  may tail-call* needs (`needsX86_closed`, …).
* `detectX86_cfg`: after detection the thresholds are `small ∈ {1, 2}`,
  `mid ∈ {4, 5, 9}` (from the defaults).  Any other value (the public setters store their
  `uint64_t` argument unclamped) is covered too: the policy compare is unsigned and every 64-bit
  value lies in a behaviour class (`Rodata.policy_ja_class`).
* `reachable`, `reachable_cfg`, `hash_x86_reachable`: after any interleaving of first calls,
  `keccaktree_init`, user overrides and setter calls (memory-model assumption below), `hash_ptr` is
  `init_and_hash`, the portable kernel, a user override, or a library kernel the CPU supports, and
  the library theorem holds for whatever thresholds the call reads.
* `hash_x86` / `hash_arm` / `hash_rv`: with the kernels' all-count theorems in a
  table of the library's shape, every `keccaktree_hash(out, in, count)` after
  `keccaktree_init(NULL)` is the portable C kernel (`Proof.hashC_spec`) or a
  library run that writes every node's digest (`LibOk`).
-/
namespace Keccaktree.Dispatch
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable Keccaktree.Asm.Library

/-- What `hash_ptr` points to. -/
inductive Impl where
  | generic
  | kernel (sym : String)
  deriving DecidableEq, Repr

/-- `keccaktree_calibrate*`: timing picks one candidate. -/
structure Oracle where
  pick : List String → Nat
  pick_lt : ∀ l : List String, l ≠ [] → pick l < l.length
  /-- `keccaktree_avx2_tail_calibrate`: the lane-pair kernel beat the padded batch -/
  pairsFaster : Bool
  /-- `keccaktree_avx2_x10_tail_calibrate`: the setting 9 beat 5 -/
  midNine : Bool

def calibrate (o : Oracle) (l : List String) : String := l.getD (o.pick l) ""

theorem calibrate_mem (o : Oracle) (l : List String) (h : l ≠ []) : calibrate o l ∈ l := by
  unfold calibrate
  have := o.pick_lt l h
  simp only [List.getD, List.getElem?_eq_getElem this, Option.getD_some]
  exact List.getElem_mem this

/-! ## x86-64 -/

/-- The CPU's report: CPUID.1:ECX.OSXSAVE, XGETBV(0), CPUID.7.0:EBX AVX2/AVX512F/AVX512VL/BMI1/BMI2. -/
structure X86Cpu where
  osxsave : Bool
  xcr0 : Nat
  avx2 : Bool
  avx512f : Bool
  avx512vl : Bool
  bmi1 : Bool
  bmi2 : Bool

def X86Cpu.osYmm (c : X86Cpu) : Bool := c.xcr0 &&& 0x6 == 0x6
def X86Cpu.osZmm (c : X86Cpu) : Bool := c.xcr0 &&& 0xe6 == 0xe6
def X86Cpu.bmi (c : X86Cpu) : Bool := c.bmi1 && c.bmi2

/-- The runtime thresholds (`.Lsmall_tail_max` of avx2_x4, `.Lmid_tail_max` of avx2_x10). -/
structure Cfg where
  small : Nat
  mid : Nat
  deriving DecidableEq, Repr

/-- The `.data` defaults. -/
def cfg0 : Cfg := ⟨1, 4⟩

def avx512List : List String := [sym "avx512_x9d", sym "avx512_x8d", sym "avx512_x8", sym "avx512vl_x4"]
def avx2List : List String := [sym "avx2_x10", sym "avx2_x5", sym "avx2_x6", sym "avx2_x8", sym "avx2_x4"]

/-- `keccaktree_detect` on x86-64 (the thresholds `cfg` before the call). -/
def detectX86 (c : X86Cpu) (o : Oracle) (cfg : Cfg) : Impl × Cfg :=
  if !c.osxsave then (.generic, cfg)
  else if c.osZmm && c.avx512f && c.avx512vl && c.bmi then (.kernel (calibrate o avx512List), cfg)
  else if c.osYmm && c.avx2 && c.bmi then
    -- keccaktree_avx2_tail_calibrate: small_tail(1), timing, small_tail(2 or 1)
    let cfg1 : Cfg := { cfg with small := if o.pairsFaster then 2 else 1 }
    let k := calibrate o avx2List
    -- keccaktree_avx2_x10_tail_calibrate only when avx2_x10 won
    let cfg2 : Cfg := if k = sym "avx2_x10" then { cfg1 with mid := if o.midNine then 9 else 5 } else cfg1
    (.kernel k, cfg2)
  else if c.bmi then (.kernel (sym "x86_x1"), cfg)
  else (.generic, cfg)

/-- The instruction-set extensions a kernel executes (its own code; tail targets separately). -/
def needsX86 (k : String) (zmm ymm a2 a512f a512vl bmi : Bool) : Bool :=
  if k = sym "x86_x1" then bmi
  else if k ∈ [sym "avx2_x2", sym "avx2_x4", sym "avx2_x5", sym "avx2_x6", sym "avx2_x8", sym "avx2_x9", sym "avx2_x10"]
    then ymm && a2 && bmi
  else if k ∈ [sym "avx512vl_x4", sym "avx512vl_x4d", sym "avx512_x8", sym "avx512_x8d", sym "avx512_x9", sym "avx512_x9d"]
    then zmm && a512f && a512vl && bmi
  else false

/-- Tail calls never need more than the caller: every target's needs follow from the caller's. -/
theorem needsX86_closed : ∀ e ∈ x86Shape, ∀ t ∈ e.2.2, ∀ zmm ymm a2 a512f a512vl bmi : Bool,
    needsX86 e.1 zmm ymm a2 a512f a512vl bmi = true → needsX86 t zmm ymm a2 a512f a512vl bmi = true := by
  decide

def x86Names : List String := x86Shape.map (·.1)

/-- **The x86 selection is sound**: the portable kernel, or a library kernel whose extensions
(and its tail targets' extensions) the CPU reports. -/
theorem detectX86_sound (c : X86Cpu) (o : Oracle) (cfg : Cfg) :
    (detectX86 c o cfg).1 = .generic ∨
    ∃ k, (detectX86 c o cfg).1 = .kernel k ∧ k ∈ x86Names ∧
      needsX86 k c.osZmm c.osYmm c.avx2 c.avx512f c.avx512vl c.bmi = true := by
  unfold detectX86
  split
  · exact Or.inl rfl
  · split
    · rename_i h1 h2
      right
      have := calibrate_mem o avx512List (by decide)
      generalize calibrate o avx512List = k at this ⊢
      simp only [Bool.and_eq_true] at h2
      simp only [avx512List, List.mem_cons, List.mem_nil_iff, or_false] at this
      refine ⟨k, rfl, ?_, ?_⟩ <;> rcases this with rfl | rfl | rfl | rfl <;> simp [needsX86, sym, h2, x86Names, x86Shape]
    · split
      · rename_i h1 h2 h3
        right
        have := calibrate_mem o avx2List (by decide)
        simp only [Bool.and_eq_true] at h3
        simp only []
        generalize calibrate o avx2List = k at this ⊢
        simp only [avx2List, List.mem_cons, List.mem_nil_iff, or_false] at this
        refine ⟨k, rfl, ?_, ?_⟩ <;> rcases this with rfl | rfl | rfl | rfl | rfl <;>
          simp [needsX86, sym, h3, x86Names, x86Shape]
      · split
        · rename_i h4
          right; exact ⟨_, rfl, by decide, by simp [needsX86, sym, h4]⟩
        · exact Or.inl rfl

/-- **The thresholds after detection** (from the `.data` defaults): `small ∈ {1, 2}`,
`mid ∈ {4, 5, 9}`; in particular both are numbers `< 2^55` (`Rodata.policy_ja_class`). -/
theorem detectX86_cfg (c : X86Cpu) (o : Oracle) :
    (detectX86 c o cfg0).2.small ∈ [1, 2] ∧ (detectX86 c o cfg0).2.mid ∈ [4, 5, 9] := by
  unfold detectX86
  split
  · simp [cfg0]
  · split
    · simp [cfg0]
    · split
      · simp only []
        split <;> (cases o.pairsFaster <;> cases o.midNine <;> simp [cfg0])
      · split <;> simp [cfg0]

/-- A name of the shape is the name of a kernel of a table of that shape. -/
theorem mem_table_of_name {isa : Isa} {EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop}
    (T : Table isa EntryAt Digest) (sh : List (String × Nat × List String)) (hT : T.shape = sh) (k : String)
    (hk : k ∈ sh.map (·.1)) : ∃ K ∈ T, K.name = k := by
  rw [← hT] at hk
  simp only [Table.shape, List.map_map, List.mem_map, Function.comp_def] at hk
  obtain ⟨K, hK, rfl⟩ := hk
  exact ⟨K, hK, rfl⟩

/-- **`keccaktree_hash` on x86-64 is correct.**  After `keccaktree_init(NULL)` (detection from the
defaults), `hash_ptr` is the portable C kernel — whose batch contract is `Proof.hashC_spec` — or a
library kernel `K` of the table for the thresholds detection left, and from the x86 entry state of
`keccaktree_hash(out, in, count)` (`EntryX86`, offset 0: the arguments are passed through) the
library run writes every node's digest without a model fault. -/
theorem hash_x86 (T : Cfg → Table X86.isa EntryX86 Digest) (hT : ∀ cfg, (T cfg).shape = x86Shape)
    (c : X86Cpu) (o : Oracle) :
    (detectX86 c o cfg0).1 = .generic ∨
    ∃ K ∈ T (detectX86 c o cfg0).2, (detectX86 c o cfg0).1 = .kernel K.name ∧
      needsX86 K.name c.osZmm c.osYmm c.avx2 c.avx512f c.avx512vl c.bmi = true ∧
      ∀ (count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
        EntryX86 K.name 0 count input S → LibOk (T (detectX86 c o cfg0).2) K 0 count input S := by
  rcases detectX86_sound c o cfg0 with h | ⟨k, hk, hmem, hneeds⟩
  · exact Or.inl h
  · right
    obtain ⟨K, hK, hname⟩ := mem_table_of_name _ x86Shape (hT _) k hmem
    subst hname
    exact ⟨K, hK, hk, hneeds, fun count input S hS => lib_x86 T hT _ K hK 0 count input S hS⟩

/-! ## The public setters, user overrides and concurrent first calls (x86-64)

The threshold setters `keccaktree_avx2_small_tail(uint64_t)` / `keccaktree_avx2_x10_mid_tail(uint64_t)`
store their argument unclamped (`mov qword ptr [rip + .L…], ARG_OUT; ret`): every 64-bit value can
reach the kernels.  Since the policy compare is unsigned (`X86.setFlagsNum`), every value lies in one
behaviour class (`Rodata.classRep`, `policy_ja_class` for all `v < 2^64`), so the library theorem is
stated for every configuration (`lib_x86`, `hash_x86_reachable`).

**Memory-model assumption for concurrent first calls**: `hash_ptr` and the two threshold words are
plain globals written without synchronisation (`hash_ptr = keccaktree_detect()` in
`init_and_hash`, the setters, the calibration).  C11 calls such races undefined; we assume what the
supported compilers emit and the hardware gives for aligned 8-byte plain stores and loads
(x86-64: aligned 8-byte accesses are atomic; AArch64 and RISC-V: single-copy atomic): a load
returns one of the values stored, never a torn mix.  Under that assumption a run is an interleaving
of whole-value events (`Event`), and every value any thread can observe is covered: `hash_ptr` is
`init_and_hash`, the result of *some* detection (with whatever thresholds that thread saw), or a
user override; the thresholds are 64-bit numbers.  Calibration runs on the shared static scratch
buffer race too; their results are discarded.
-/

/-- What `hash_ptr` holds: `init_and_hash` (detect on first call), or an implementation. -/
abbrev Ptr := Option Impl

/-- The process-global state: `hash_ptr` and the two threshold words. -/
structure ApiState where
  ptr : Ptr
  cfg : Cfg

def apiInit : ApiState := ⟨none, cfg0⟩

/-- Whole-value writes to the globals (any thread, any order). -/
inductive Event where
  /-- a detection finished (oracle `o`, having seen thresholds `seen`) and stored its result -/
  | detectStore (o : Oracle) (seen : Cfg)
  /-- `keccaktree_init(f)` with a non-null override -/
  | override (f : Impl)
  /-- `keccaktree_avx2_small_tail(v)` (by the user, or the calibration) -/
  | writeSmall (v : Nat)
  /-- `keccaktree_avx2_x10_mid_tail(v)` -/
  | writeMid (v : Nat)

def applyEvent (c : X86Cpu) (st : ApiState) : Event → ApiState
  | .detectStore o seen => { st with ptr := some (detectX86 c o seen).1 }
  | .override f => { st with ptr := some f }
  | .writeSmall v => { st with cfg := { st.cfg with small := v % 2 ^ 64 } }
  | .writeMid v => { st with cfg := { st.cfg with mid := v % 2 ^ 64 } }

def overrides : List Event → List Impl
  | [] => []
  | .override f :: es => f :: overrides es
  | _ :: es => overrides es

/-- The values `hash_ptr` may hold: `init_and_hash`, the portable kernel, a library kernel whose
extensions the CPU reports, or one of the user's overrides `ovs`. -/
def GoodPtr (c : X86Cpu) (ovs : List Impl) (p : Ptr) : Prop :=
  p = none ∨ p = some .generic ∨
  (∃ k, p = some (.kernel k) ∧ k ∈ x86Names ∧ needsX86 k c.osZmm c.osYmm c.avx2 c.avx512f c.avx512vl c.bmi = true) ∨
  ∃ f ∈ ovs, p = some f

theorem GoodPtr.mono {c : X86Cpu} {ovs : List Impl} {p : Ptr} (h : GoodPtr c ovs p) (more : List Impl) :
    GoodPtr c (ovs ++ more) p := by
  rcases h with h | h | h | ⟨f, hf, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨f, List.mem_append_left _ hf, h⟩))

theorem goodPtr_detect (c : X86Cpu) (o : Oracle) (seen : Cfg) (ovs : List Impl) :
    GoodPtr c ovs (some (detectX86 c o seen).1) := by
  rcases detectX86_sound c o seen with h | ⟨k, hk, hmem, hn⟩
  · exact Or.inr (Or.inl (by rw [h]))
  · exact Or.inr (Or.inr (Or.inl ⟨k, by rw [hk], hmem, hn⟩))

/-- **Every observable `hash_ptr`**, after any interleaving of whole-value events. -/
theorem reachable (c : X86Cpu) :
    ∀ (es : List Event) (st : ApiState) (ovs : List Impl), GoodPtr c ovs st.ptr →
      GoodPtr c (ovs ++ overrides es) (es.foldl (applyEvent c) st).ptr
  | [], st, ovs, h => by simpa [overrides] using h
  | e :: es, st, ovs, h => by
    simp only [List.foldl_cons]
    cases e with
    | detectStore o seen =>
      have := reachable c es (applyEvent c st (.detectStore o seen)) ovs (goodPtr_detect c o seen ovs)
      simpa [overrides] using this
    | override f =>
      have h1 : GoodPtr c (ovs ++ [f]) (applyEvent c st (.override f)).ptr :=
        Or.inr (Or.inr (Or.inr ⟨f, by simp, rfl⟩))
      have := reachable c es _ _ h1
      simpa [overrides, List.append_assoc] using this
    | writeSmall v => simpa [overrides] using reachable c es (applyEvent c st (.writeSmall v)) ovs h
    | writeMid v => simpa [overrides] using reachable c es (applyEvent c st (.writeMid v)) ovs h

/-- The thresholds are always 64-bit numbers (the setters store a `uint64_t`). -/
theorem reachable_cfg (c : X86Cpu) :
    ∀ (es : List Event) (st : ApiState), st.cfg.small < 2 ^ 64 → st.cfg.mid < 2 ^ 64 →
      (es.foldl (applyEvent c) st).cfg.small < 2 ^ 64 ∧ (es.foldl (applyEvent c) st).cfg.mid < 2 ^ 64
  | [], st, hs, hm => ⟨hs, hm⟩
  | e :: es, st, hs, hm => by
    simp only [List.foldl_cons]
    cases e with
    | writeSmall v => exact reachable_cfg c es _ (Nat.mod_lt _ (by decide)) hm
    | writeMid v => exact reachable_cfg c es _ hs (Nat.mod_lt _ (by decide))
    | _ => exact reachable_cfg c es _ hs hm

/-- **`keccaktree_hash` in any reachable state** (any interleaving of first calls, `keccaktree_init`,
setter calls; under the memory-model assumption above): the call runs `init_and_hash` (a detection,
then one of the implementations below), the portable kernel, a user override (outside the library),
or a library kernel, for which the library theorem holds with the thresholds the call reads —
whatever 64-bit values they hold. -/
theorem hash_x86_reachable (T : Cfg → Table X86.isa EntryX86 Digest) (hT : ∀ cfg, (T cfg).shape = x86Shape)
    (c : X86Cpu) (es : List Event) :
    let st := es.foldl (applyEvent c) apiInit
    st.ptr = none ∨ st.ptr = some .generic ∨ (∃ f ∈ overrides es, st.ptr = some f) ∨
    ∃ k, st.ptr = some (.kernel k) ∧ needsX86 k c.osZmm c.osYmm c.avx2 c.avx512f c.avx512vl c.bmi = true ∧
      ∀ cfg : Cfg, ∃ K ∈ T cfg, K.name = k ∧
        ∀ (count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
          EntryX86 k 0 count input S → LibOk (T cfg) K 0 count input S := by
  have h := reachable c es apiInit [] (Or.inl rfl)
  simp only [List.nil_append] at h
  rcases h with h | h | ⟨k, hk, hmem, hn⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inr ⟨k, hk, hn, fun cfg => ?_⟩))
    obtain ⟨K, hK, hname⟩ := mem_table_of_name _ x86Shape (hT cfg) k hmem
    subst hname
    exact ⟨K, hK, rfl, fun count input S hS => lib_x86 T hT cfg K hK 0 count input S hS⟩
  · exact Or.inr (Or.inr (Or.inl h))

/-! ## AArch64 -/

inductive Os where
  | linux | apple | other
  deriving DecidableEq, Repr

/-- The report: FEAT_SHA3 (`HWCAP_SHA3`, or the `hw.optional` sysctls), Advanced SIMD (`HWCAP_ASIMD`),
and whether the C library's headers define `HWCAP_SHA3`. -/
structure ArmCpu where
  os : Os
  sha3 : Bool
  asimd : Bool
  hwcapSha3Defined : Bool

def sha3List : List String := [sym "sha3_x3", sym "sha3_x3r", sym "sha3_x2"]
def simdList : List String := [sym "neon_x3", sym "scalar_x1", sym "neon_x2"]

def detectArm (c : ArmCpu) (o : Oracle) : Impl :=
  match c.os with
  | .apple => if c.sha3 then .kernel (calibrate o sha3List) else .kernel (calibrate o simdList)
  | .linux =>
    if c.hwcapSha3Defined && c.sha3 then .kernel (calibrate o sha3List)
    else if c.asimd then .kernel (calibrate o simdList) else .generic
  | .other => .generic

def needsArm (k : String) (sha3 : Bool) : Bool :=
  if k ∈ [sym "sha3_x2", sym "sha3_x3", sym "sha3_x3r"] then sha3 else k ∈ armShape.map (·.1)

theorem needsArm_closed : ∀ e ∈ armShape, ∀ t ∈ e.2.2, ∀ sha3 : Bool,
    needsArm e.1 sha3 = true → needsArm t sha3 = true := by
  decide

theorem detectArm_sound (c : ArmCpu) (o : Oracle) :
    detectArm c o = .generic ∨ ∃ k, detectArm c o = .kernel k ∧ k ∈ armShape.map (·.1) ∧ needsArm k c.sha3 = true := by
  have hs := calibrate_mem o sha3List (by decide)
  have hn := calibrate_mem o simdList (by decide)
  unfold detectArm
  generalize calibrate o sha3List = ks at hs ⊢
  generalize calibrate o simdList = kn at hn ⊢
  simp only [sha3List, simdList, List.mem_cons, List.mem_nil_iff, or_false] at hs hn
  split
  · split
    · rename_i h; right; refine ⟨_, rfl, ?_⟩
      rcases hs with h' | h' | h' <;> rw [h'] <;> simp [needsArm, sym, armShape, h]
    · right; refine ⟨_, rfl, ?_⟩
      rcases hn with h' | h' | h' <;> rw [h'] <;> simp [needsArm, sym, armShape]
  · split
    · rename_i h; simp only [Bool.and_eq_true] at h; right; refine ⟨_, rfl, ?_⟩
      rcases hs with h' | h' | h' <;> rw [h'] <;> simp [needsArm, sym, armShape, h]
    · split
      · right; refine ⟨_, rfl, ?_⟩
        rcases hn with h' | h' | h' <;> rw [h'] <;> simp [needsArm, sym, armShape]
      · exact Or.inl rfl
  · exact Or.inl rfl

theorem hash_arm (T : Table Arm.isa EntryArm Digest) (hT : T.shape = armShape) (c : ArmCpu) (o : Oracle) :
    detectArm c o = .generic ∨
    ∃ K ∈ T, detectArm c o = .kernel K.name ∧ needsArm K.name c.sha3 = true ∧
      ∀ (count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
        EntryArm K.name 0 count input S → LibOk T K 0 count input S := by
  rcases detectArm_sound c o with h | ⟨k, hk, hmem, hneeds⟩
  · exact Or.inl h
  · right
    obtain ⟨K, hK, hname⟩ := mem_table_of_name T armShape hT k hmem
    subst hname
    exact ⟨K, hK, hk, hneeds, fun count input S hS => lib_arm T hT K hK 0 count input S hS⟩

/-! ## RISC-V -/

/-- The report: `riscv_hwprobe` (Linux; IMA_EXT_0: V, Zbb, Zvkb) and `vlenb`. -/
structure RvCpu where
  linux : Bool
  hwprobeOk : Bool
  extV : Bool
  extZbb : Bool
  extZvkb : Bool
  vlenb : Nat

def RvCpu.v (c : RvCpu) : Bool := c.linux && c.hwprobeOk && c.extV && decide (c.vlenb ≥ 16)
def RvCpu.zbb (c : RvCpu) : Bool := c.linux && c.hwprobeOk && c.extZbb
def RvCpu.zvkb (c : RvCpu) : Bool := c.linux && c.hwprobeOk && c.extZvkb

def rvCands (zbb v zvkb : Bool) : List String :=
  [sym "rv64_x1"] ++ (if zbb then [sym "zbb_x1"] else []) ++ (if v then [sym "rvv"] else []) ++
    (if v && zvkb then [sym "rvv_zvkb"] else [])

def rvCandidates (c : RvCpu) : List String := rvCands c.zbb c.v c.zvkb

def detectRv (c : RvCpu) (o : Oracle) : Impl := .kernel (calibrate o (rvCandidates c))

def needsRv (k : String) (zbb v zvkb : Bool) : Bool :=
  if k = sym "rv64_x1" then true else if k = sym "zbb_x1" then zbb
  else if k = sym "rvv" then v else if k = sym "rvv_zvkb" then v && zvkb else false

/-- RISC-V: a library kernel the CPU supports; the vector kernels only with `VLEN ≥ 128`
(`vlenb ≥ 16`), and their proofs are per vector length (`lib_rv vlmax`, `vlmax = vlenb / 8`). -/
theorem detectRv_sound (c : RvCpu) (o : Oracle) :
    ∃ k, detectRv c o = .kernel k ∧ k ∈ rvShape.map (·.1) ∧ needsRv k c.zbb c.v c.zvkb = true := by
  have h := calibrate_mem o (rvCandidates c) (by simp [rvCandidates, rvCands])
  refine ⟨_, rfl, ?_⟩
  generalize calibrate o (rvCandidates c) = k at h ⊢
  have key : ∀ zbb v zvkb : Bool, ∀ k ∈ rvCands zbb v zvkb, k ∈ rvShape.map (·.1) ∧ needsRv k zbb v zvkb = true := by
    decide
  exact key c.zbb c.v c.zvkb k h

theorem hash_rv (vlmax : Nat) (T : Table (Riscv.isa vlmax) EntryRv Digest) (hT : T.shape = rvShape) (c : RvCpu)
    (o : Oracle) :
    ∃ K ∈ T, detectRv c o = .kernel K.name ∧ needsRv K.name c.zbb c.v c.zvkb = true ∧
      ∀ (count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
        EntryRv K.name 0 count input S → LibOk T K 0 count input S := by
  obtain ⟨k, hk, hmem, hneeds⟩ := detectRv_sound c o
  obtain ⟨K, hK, hname⟩ := mem_table_of_name T rvShape hT k hmem
  subst hname
  exact ⟨K, hK, hk, hneeds, fun count input S hS => lib_rv vlmax T hT K hK 0 count input S hS⟩

end Keccaktree.Dispatch
