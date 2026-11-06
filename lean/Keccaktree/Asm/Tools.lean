import Keccaktree.Asm.Exec
import Keccaktree.Asm.Arm
import Keccaktree.Asm.Riscv
import Keccaktree.Asm.Compose
import Std.Data.HashMap
/-!
Proof-generation tools (run with `#eval`; nothing here is trusted):

* `E.toLean`, `State.toLean`: print symbolic states as Lean terms, for the
  slice lemmas that the kernel checks by `rfl`;
* the matcher: run a kernel on two random inputs and, after every
  instruction, find for each register lane and memory word which
  specification quantity it holds (node, round, lane or theta-D, rotation);
  this discovers the kernels' round boundaries and register allocations.
-/
namespace Keccaktree.Asm.X86.Tools
open Keccaktree.Asm Keccak

instance : Inhabited Spec.State := ⟨⟨fun _ _ => 0#64⟩⟩

def hex (v : BitVec 64) : String := "0x" ++ String.ofList (Nat.toDigits 16 v.toNat) ++ "#64"

def _root_.Keccaktree.Asm.E.toLean : E → String
  | .var i => s!"(.var {i})"
  | .const v => s!"(.const {hex v})"
  | .xor a b => s!"(.xor {E.toLean a} {E.toLean b})"
  | .and a b => s!"(.and {E.toLean a} {E.toLean b})"
  | .or a b => s!"(.or {E.toLean a} {E.toLean b})"
  | .not a => s!"(.not {E.toLean a})"
  | .shl a n => s!"(.shl {E.toLean a} {n})"
  | .shr a n => s!"(.shr {E.toLean a} {n})"
  | .rol a n => s!"(.rol {E.toLean a} {n})"
  | .add a b => s!"(.add {E.toLean a} {E.toLean b})"

def _root_.Keccaktree.Asm.E.size : E → Nat
  | .var _ => 1 | .const _ => 1
  | .xor a b | .and a b | .or a b | .add a b => 1 + a.size + b.size
  | .not a | .shl a _ | .shr a _ | .rol a _ => 1 + a.size

def addrToLean (a : Addr) : String := s!"⟨{a.region}, ({a.off})⟩"

/-- What the tools need of an instruction set (no proofs: the executable side of `Isa`). -/
structure IsaTool where
  name : String                                     -- the Lean name of the `Isa` (`X86.isa`, `Arm.isa`)
  Instr : Type
  exec : {α : Type} → [LaneOps α] → Array (BitVec 64) → Instr → State α → State α
  nop : Instr
  /-- The cells an instruction stores, from the state before it. -/
  storeCells : {α : Type} → [LaneOps α] → State α → Instr → List (Region × Int)
  initState : {α : Type} → [LaneOps α] → (Int → α) → α → Nat → Nat → State α
  /-- The register holding the remaining count (for tails). -/
  countOf : State (BitVec 64) → Nat

def IsaTool.execTrace (T : IsaTool) [LaneOps α] (rodata : Array (BitVec 64)) (l : List T.Instr) (s : State α) : State α :=
  l.foldl (fun s i => T.exec rodata i s) s

def IsaTool.step (T : IsaTool) [LaneOps α] (rodata : Array (BitVec 64)) (prog : Array T.Instr) (s : State α) : State α :=
  T.exec rodata (prog.getD s.pc T.nop) s

variable (T : IsaTool)

/-- The stores an x86 instruction performs, as (region, word) cells, from the
state before it. -/
def x86StoreCells [LaneOps α] (s : State α) : Instr → List (Region × Int)
  | .vstore lanes dst _ => let a := memAddr s dst; (List.range lanes).map fun (i : Nat) => (a.region, a.off / 8 + Int.ofNat i)
  | .storeq m _ => let a := memAddr s m; [(a.region, a.off / 8)]
  | .push _ | .call _ => let sp := s.getG 4; [(sp.region, sp.off / 8 - 1)]
  | _ => []

def x86Tool : IsaTool :=
  { name := "X86.isa", Instr := Instr, exec := exec, nop := .nop, storeCells := x86StoreCells,
    initState := fun input zero count entry => initState input zero count entry, countOf := fun s => (s.getG 2).off.toNat }

/-- The stores an AArch64 instruction performs. -/
def armStoreCells [LaneOps α] (s : State α) : Arm.Instr → List (Region × Int)
  | .str r base off => match Arm.addr s base off with
    | some a => (List.range (Arm.regSize r / 8).toNat).map fun (i : Nat) => (a.region, a.off / 8 + Int.ofNat i)
    | none => []
  | .stp r1 r2 base off wb => match Arm.addr s base (if wb = 2 then 0 else off) with
    | some a => (List.range ((Arm.regSize r1 + Arm.regSize r2) / 8).toNat).map fun (i : Nat) => (a.region, a.off / 8 + Int.ofNat i)
    | none => []
  | _ => []

def armTool : IsaTool :=
  { name := "Arm.isa", Instr := Arm.Instr, exec := Arm.exec, nop := .nop, storeCells := armStoreCells,
    initState := Arm.initState, countOf := fun s => ((Arm.gx s 2).getD ⟨0, 0⟩).off.toNat }

/-- The stores a RISC-V instruction performs. -/
def riscvStoreCells [LaneOps α] (s : State α) : Riscv.Instr → List (Region × Int)
  | .sd _ base off => match Arm.addr s base off with
    | some a => [(a.region, a.off / 8)]
    | none => []
  | .vsseg _ base nf => match Arm.addr s base 0 with
    | some a => (List.range (nf * s.vl)).map fun (i : Nat) => (a.region, a.off / 8 + Int.ofNat i)
    | none => []
  | _ => []

def riscvTool (vlmax : Nat) : IsaTool :=
  { name := s!"(Riscv.isa {vlmax})", Instr := Riscv.Instr, exec := Riscv.exec vlmax, nop := .nop, storeCells := riscvStoreCells,
    initState := Riscv.initState, countOf := fun s => ((Arm.gx s 12).getD ⟨0, 0⟩).off.toNat }

/-- Run a slice symbolically from a cut state. -/
def symRun (rodata : Array (BitVec 64)) (prog : Array T.Instr) (idx : List Nat) (s : State E) : State E :=
  T.execTrace rodata (idx.map (prog.getD · T.nop)) s

/-- The variables of an expression. -/
partial def _root_.Keccaktree.Asm.E.vars : E → List Nat
  | .var i => [i]
  | .const _ => []
  | .xor a b | .and a b | .or a b | .add a b => a.vars ++ b.vars
  | .not a | .shl a _ | .shr a _ | .rol a _ => a.vars

/-- The state before the first failing instruction of a symbolic slice run, and its position. -/
def firstFail (rodata : Array (BitVec 64)) (prog : Array T.Instr) (idx : List Nat) (s : State E) : Option (State E × Nat) := Id.run do
  let mut st := s
  let mut n := 0
  for i in idx do
    let st' := T.exec rodata (prog.getD i T.nop) st
    if st'.err then return some (st, n)
    st := st'; n := n + 1
  return none

/-- The control words of a slice: the cut variables that must be constants for
the symbolic run to succeed (pointers and counts in data registers and stack
cells), found by fixpoint: on a failure, the general register that holds a bare
variable and whose constant lets the run get further is made control. -/
partial def findCtl (rodata : Array (BitVec 64)) (prog : Array T.Instr) (idx : List Nat) (sc : State (BitVec 64))
    (ctl : List Nat) : IO (List Nat) := do
  match firstFail T rodata prog idx (cutOf ctl sc) with
  | none => return ctl
  | some (st, n) =>
    -- the general registers' variables, and the stack cells that are still variables (saved pointers, return addresses)
    let stackCells := (List.range 1024).filterMap fun (i : Nat) =>
      let q : Int := 131072 - 1024 + Int.ofNat i
      match st.mem rStack q with | .var v => some v | _ => none
    let cands := (st.gd.toList.flatMap E.vars ++ stackCells).eraseDups.filter (!ctl.contains ·)
    let advances (extra : List Nat) : Bool :=
      match firstFail T rodata prog idx (cutOf (extra ++ ctl) sc) with
      | none => true
      | some (_, n') => n' > n
    for c in cands do
      if advances [c] then return ← findCtl rodata prog idx sc (c :: ctl)
    -- an instruction needing several words at once (`bne t1, t2`): all bare-variable registers, minimised
    if advances cands then
      let mut keep := cands
      for c in cands do
        if advances (keep.erase c) then keep := keep.erase c
      return ← findCtl rodata prog idx sc (keep ++ ctl)
    throw (IO.userError s!"symbolic slice fails at step {n} (instruction {idx.getD n 0}); no control variable fixes it")

/-! ## Matching locations against the specification -/

/-- What a location may hold: lane `k` of a node's state after `round`
rounds, theta's `D[x]` or the column parity `C[x]` of that state, rotated
left by `rot`. -/
structure Match where
  node : Nat
  round : Nat
  kind : Nat    -- 0..24 lane, 25..29 D[x], 30..34 C[x]
  rot : Nat
  deriving Repr, BEq, Hashable, Inhabited

def nKinds : Nat := 75

/-- Node `n` of the message `fun i => input word` as the state after `r` rounds. -/
def nodeState (input : Int → BitVec 64) (n r : Nat) : Spec.State :=
  let bytes : Nat → BitVec 8 := fun i => ((input (Int.ofNat (8 * n + i / 8))) >>> (8 * (i % 8))).truncate 8
  Spec.rounds r (Spec.absorb ⟨fun _ _ => 0#64⟩ (fun i => Spec.padded 64 bytes (136 * 0 + i)))

/-- The 30 spec quantities of every node and round, materialised (the spec's
own states are lazy closures; reading them repeatedly is slow). -/
def specTable (input : Int → BitVec 64) (nodes : Nat) : Array (Array (Array (BitVec 64))) :=
  Array.ofFn fun n : Fin nodes => Array.ofFn fun r : Fin 25 =>
    let A := nodeState input n r
    Array.ofFn fun kind : Fin nKinds => specQuantity A kind

/-- All (value ↦ match) pairs for `nodes` nodes. -/
def table (spec : Array (Array (Array (BitVec 64)))) : Std.HashMap (BitVec 64) (List Match) := Id.run do
  let mut t : Std.HashMap (BitVec 64) (List Match) := {}
  for n in [0:spec.size] do
    for r in [0:25] do
      for kind in [0:nKinds] do
        let q := ((spec.getD n #[]).getD r #[]).getD kind 0
        for rot in [0:64] do
          let v := q.rotateLeft rot
          t := t.insert v (⟨n, r, kind, rot⟩ :: t.getD v [])
  return t

/-- A pseudo-random input (word index ↦ word) from a seed. -/
def randInput (seed : Nat) (q : Int) : BitVec 64 :=
  if q < 0 then 0 else
  let x := (q.toNat + 1) * 0x9E3779B97F4A7C15 + seed * 0xD1B54A32D192ED03
  let x := x ^^^ (x >>> 31)
  BitVec.ofNat 64 (x * 0xBF58476D1CE4E5B9 % 2 ^ 64)

inductive Loc where
  | reg (r l : Nat)
  | gd (n : Nat)
  | mem (region : Region) (q : Int)
  deriving Repr, BEq, Inhabited

def Loc.toLean : Loc → String
  | .reg r l => s!"(.reg {r} {l})"
  | .gd n => s!"(.gd {n})"
  | .mem r q => s!"(.mem {r} ({q}))"

/-- The locations to inspect: all register lanes, and the memory words of
each region in the given windows. -/
def locations (lanes : Nat) (windows : List (Region × Int × Int)) : List Loc :=
  ((List.range 32).flatMap fun r => (List.range lanes).map fun l => Loc.reg r l) ++
  ((List.range 32).map fun n => Loc.gd n) ++
  windows.flatMap fun (region, lo, hi) => (List.range (hi - lo).toNat).map fun (i : Nat) => Loc.mem region (lo + Int.ofNat i)

/-- A run with a shadow copy of the stored memory words (the model's memory
is a chain of updates, too slow to read hundreds of words after every
instruction). -/
structure Run where
  s : State (BitVec 64)
  shadow : Std.HashMap (Region × Int) (BitVec 64)
  input : Int → BitVec 64
  rodata : Array (BitVec 64)

def Run.init (rodata : Array (BitVec 64)) (input : Int → BitVec 64) (count entry : Nat) : Run :=
  ⟨T.initState input 0 count entry, {}, input, rodata⟩

def Run.step (prog : Array T.Instr) (r : Run) : Run :=
  let ins := prog.getD r.s.pc T.nop
  let cells := T.storeCells r.s ins
  let s' := T.step r.rodata prog r.s
  ⟨s', cells.foldl (fun sh (reg, q) => sh.insert (reg, q) (s'.mem reg q)) r.shadow, r.input, r.rodata⟩

def Run.read (r : Run) : Loc → BitVec 64
  | .reg reg l => (r.s.getV reg).getD l 0
  | .gd n => r.s.gd.getD n 0
  | .mem region q =>
    match r.shadow[(region, q)]? with
    | some v => v
    | none => if region = rInput then r.input q else 0

/-- Matches of every location in two runs (same control flow). -/
def matchAll (t1 : Std.HashMap (BitVec 64) (List Match)) (spec2 : Array (Array (Array (BitVec 64))))
    (locs : List Loc) (r1 r2 : Run) : List (Loc × Match) :=
  locs.filterMap fun loc =>
    let v1 := r1.read loc
    let v2 := r2.read loc
    -- constants (zero lanes, untouched memory) carry no information
    if v1 == v2 then none else
    let cands0 := t1.getD v1 []
    if cands0.length > 256 then none else
    let cands := cands0.filter fun m =>
      (((spec2.getD m.node #[]).getD m.round #[]).getD m.kind 0).rotateLeft m.rot == v2
    match cands with
    | [m] => some (loc, m)
    | _ => none

/-- Step both runs for `n` instructions from the entry, reporting after each
instruction the executed index and, per node, the rounds whose 25 lanes are
all present somewhere (plus which D's). Output lines: `t idx node:rounds...`. -/
def scan (prog : Array T.Instr) (rodata : Array (BitVec 64)) (entry count fuel lanes : Nat)
    (windows : List (Region × Int × Int)) : IO Unit := do
  let in1 := randInput 1
  let in2 := randInput 2
  let t1 := table (specTable in1 count)
  let spec2 := specTable in2 count
  let locs := locations lanes windows
  let mut s1 := Run.init T rodata in1 count entry
  let mut s2 := Run.init T rodata in2 count entry
  let mut tStep := 0; let mut tMatch := 0; let mut tSum := 0
  for t in [0:fuel] do
    if s1.s.halted then break
    let i := s1.s.pc
    let c0 ← IO.monoMsNow
    s1 := s1.step T prog
    s2 := s2.step T prog
    let c1 ← IO.monoMsNow
    let ms := matchAll t1 spec2 locs s1 s2
    let c2 ← IO.monoMsNow
    tStep := tStep + (c1 - c0); tMatch := tMatch + (c2 - c1)
    if t % 200 == 199 then IO.eprintln s!"t={t} step={tStep}ms match={tMatch}ms sum={tSum}ms shadow={s1.shadow.size} ms={ms.length}"
    -- per node and round: number of distinct lanes present
    let mut summary := ""
    for n in [0:count] do
      let mut parts := ""
      for r in [0:25] do
        let lanesHere := (ms.filter fun (_, m) => m.node == n && m.round == r && m.kind < 25).map (·.2.kind) |>.eraseDups
        let ds := (ms.filter fun (_, m) => m.node == n && m.round == r && m.kind ≥ 25 && m.kind < 30).map (·.2.kind) |>.eraseDups
        let cs := (ms.filter fun (_, m) => m.node == n && m.round == r && m.kind ≥ 30).map (·.2.kind) |>.eraseDups
        if lanesHere.length > 0 || ds.length > 0 || cs.length > 0 then
          parts := parts ++ s!" r{r}:{lanesHere.length}L{ds.length}D{cs.length}C"
      summary := summary ++ s!" n{n}:[{parts} ]"
    let c3 ← IO.monoMsNow
    tSum := tSum + (c3 - c2)
    IO.println s!"{t} {i}{summary}"

/-- Probe: per step, only read the register lanes and look them up. -/
def probe (prog : Array T.Instr) (rodata : Array (BitVec 64)) (entry count fuel lanes : Nat) : IO Unit := do
  let in1 := randInput 1
  let t1 := table (specTable in1 count)
  let locs := locations lanes []
  let mut s1 := Run.init T rodata in1 count entry
  let mut hits := 0
  let mut tRead := 0; let mut tLook := 0
  for t in [0:fuel] do
    if s1.s.halted then break
    s1 := s1.step T prog
    let c0 ← IO.monoMsNow
    let vs := locs.map s1.read
    let c1 ← IO.monoMsNow
    for v in vs do
      if (t1.getD v []).length > 0 then hits := hits + 1
    let c2 ← IO.monoMsNow
    tRead := tRead + (c1 - c0); tLook := tLook + (c2 - c1)
    if t % 200 == 199 then IO.eprintln s!"t={t} read={tRead}ms lookup={tLook}ms hits={hits}"

/-- Probe: cost of reading spec quantities from the spec table. -/
def probeSpec (count reps : Nat) : IO Unit := do
  let in2 := randInput 2
  let c0 ← IO.monoMsNow
  let spec2 := specTable in2 count
  let c1 ← IO.monoMsNow
  IO.eprintln s!"table: {c1 - c0}ms"
  let mut acc : BitVec 64 := 0
  for r in [0:25] do
    let d0 ← IO.monoMsNow
    for _ in [0:reps] do
      for n in [0:count] do
        for kind in [0:30] do
          acc := acc ^^^ ((spec2.getD n #[]).getD r #[]).getD kind 0
    let d1 ← IO.monoMsNow
    IO.eprintln s!"round {r}: {d1 - d0}ms for {reps * count * 30} reads"
  IO.println s!"{acc}"

/-- Print, for the trace positions `[a, b)` of the concrete run: the executed
instruction indices, the control part of the state at `a` (as a `cutOf`-shaped
literal) and the symbolic result of running the slice from the cut state. -/
def scLit (c : State (BitVec 64)) (cells : List (Nat × Int × BitVec 64)) : String :=
  s!"(State.mk (Vector.replicate 32 (Vector.replicate 8 (0#64))) #v[{", ".intercalate (c.g.toList.map fun a => s!"(Addr.mk {a.region} ({a.off}))")}] #v[{", ".intercalate (c.gd.toList.map hex)}] #v[{", ".intercalate (c.k.toList.map toString)}] {c.zf} {c.cf} {c.nf} {c.vf} {c.vl} (memLit [{", ".intercalate (cells.map fun (r, q, w) => s!"({r}, ({q}), {hex w})")}]) {c.pc} {c.depth} false false none)"

/-- The control words of the slice `[a, b)` and the literal cut: `CTL`, `SC`, `IDX`,
`ERR`, and the symbolic result (`VAR`). -/
def sliceLit (prog : Array T.Instr) (rodata : Array (BitVec 64)) (entry count a b : Nat) : IO Unit := do
  let in1 := randInput 1
  let mut r := Run.init T rodata in1 count entry
  let mut idx : Array Nat := #[]
  for t in [0:b] do
    if t ≥ a then idx := idx.push r.s.pc
    r := r.step T prog
  let mut c0 := Run.init T rodata in1 count entry
  for _ in [0:a] do c0 := c0.step T prog
  let ctl0 ← findCtl T rodata prog idx.toList c0.s []
  -- `KT_CTL=v1,v2,..`: control words to add (the union over all slices of a batch)
  let extra := ((← IO.getEnv "KT_CTL").getD "").splitOn "," |>.filterMap (·.toNat?)
  let ctl := (ctl0 ++ extra).eraseDups
  let cells := ctl.filterMap fun i => if i ≥ 288 then some ((memVarRegion i).val, memVarIndex i, envOf c0.s i) else none
  IO.println s!"CTL {ctl}"
  IO.println s!"SC {scLit c0.s cells}"
  IO.println s!"IDX {idx.toList}"
  let cut := cutOf ctl c0.s
  let res := symRun T rodata prog idx.toList cut
  IO.println s!"ERR {res.err} MAXTREE {(res.v.toList.flatMap (·.toList)).foldl (fun m e => max m e.size) 0}"
  for reg in [0:32] do
    for l in [0:8] do
      IO.println s!"VAR {regVar reg l} {E.toLean (readVar res (regVar reg l))}"
  for n in [0:32] do
    IO.println s!"VAR {gdVar n} {E.toLean (readVar res (gdVar n))}"
  let mut cells : List (Region × Int) := []
  let mut rs := c0.s
  for i in idx.toList do
    let ins := prog.getD i T.nop
    cells := cells ++ T.storeCells rs ins
    rs := T.exec rodata ins rs
  for (reg, q) in cells.eraseDups do
    IO.println s!"VAR {memVar reg q} {E.toLean (res.mem reg q)}"
  for i in ctl do
    if i ≥ 288 && !(cells.contains (memVarRegion i, memVarIndex i)) then
      IO.println s!"VAR {i} {E.toLean (res.mem (memVarRegion i) (memVarIndex i))}"

/-- Numeric check of the symbolic slice machinery: evaluate the symbolic
result of the slice `[a, b)` under the concrete values at `a` and compare
with the concrete state at `b`. -/
def checkSlice (prog : Array T.Instr) (rodata : Array (BitVec 64)) (entry count a b : Nat) : IO Unit := do
  let in1 := randInput 1
  let mut r := Run.init T rodata in1 count entry
  let mut idx : Array Nat := #[]
  for t in [0:b] do
    if t ≥ a then idx := idx.push r.s.pc
    r := r.step T prog
  let sb := r.s
  let mut ra := Run.init T rodata in1 count entry
  for _ in [0:a] do ra := ra.step T prog
  let sa := ra.s
  let ctl ← findCtl T rodata prog idx.toList sa []
  IO.println s!"CTL {ctl}"
  let cut := cutOf ctl sa
  let res := symRun T rodata prog idx.toList cut
  let env := envOf sa
  let mut bad := 0
  for reg in [0:32] do
    for l in [0:8] do
      let sym := E.eval env (readVar res (regVar reg l))
      let con := (sb.getV reg).getD l 0
      if sym != con then
        bad := bad + 1
        if bad ≤ 10 then IO.println s!"MISMATCH reg {reg} lane {l}: sym={hex sym} con={hex con}"
  -- memory: the cells stored by the slice (from the instruction stream)
  let mut cells : List (Region × Int) := []
  let mut rs := ra.s
  for i in idx.toList do
    let ins := prog.getD i T.nop
    cells := cells ++ T.storeCells rs ins
    rs := T.exec rodata ins rs
  let cellsU := cells.eraseDups
  for (reg, q) in cellsU do
    let sym := E.eval env (res.mem reg q)
    let con := sb.mem reg q
    if sym != con then
      bad := bad + 1
      if bad ≤ 10 then IO.println s!"MISMATCH mem {reg} {q}: sym={hex sym} con={hex con}"
  IO.println s!"checked {256 + cellsU.length} locations, {bad} mismatches; g equal: {res.g == sb.g}, k equal: {res.k == sb.k}"

/-- The full match list at one point (after `n` instructions). -/
def matchesAt (prog : Array T.Instr) (rodata : Array (BitVec 64)) (entry count n lanes : Nat)
    (windows : List (Region × Int × Int)) : IO Unit := do
  let in1 := randInput 1
  let in2 := randInput 2
  let t1 := table (specTable in1 count)
  let spec2 := specTable in2 count
  let locs := locations lanes windows
  let mut s1 := Run.init T rodata in1 count entry
  let mut s2 := Run.init T rodata in2 count entry
  for _ in [0:n] do
    s1 := s1.step T prog
    s2 := s2.step T prog
  for (loc, m) in matchAll t1 spec2 locs s1 s2 do
    IO.println s!"{loc.toLean} {m.node} {m.round} {m.kind} {m.rot}"
  IO.println s!"CONTROL g={s1.s.g.toList.map addrToLean} gd={s1.s.gd.toList.map hex} k={s1.s.k.toList} zf={s1.s.zf} cf={s1.s.cf} nf={s1.s.nf} vf={s1.s.vf} vl={s1.s.vl} pc={s1.s.pc} depth={s1.s.depth}"

end Keccaktree.Asm.X86.Tools
