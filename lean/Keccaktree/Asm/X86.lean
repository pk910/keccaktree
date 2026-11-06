import Keccaktree.Asm.Machine
/-!
# x86-64 (AVX2 / AVX-512) kernel semantics

The instruction subset of `src/keccak256_avx2_*.S` and
`src/keccak256_avx512*.S` (see `lean/asm2lean.py`, which translates
`objdump -d -r` output into `Instr` literals).  Vector registers are 8
lanes of 64 bits (zmm); ymm/xmm forms work on the low 4/2 lanes and zero
the rest (VEX/EVEX zeroing).  Memory operands are `[gpr + disp]`, or
rip-relative references into the read-only data region (`.rodata`),
resolved by the translator to region/offset.
-/

namespace Keccaktree.Asm.X86

/-- General registers by number: 0 rax, 1 rcx, 2 rdx, 3 rbx, 4 rsp, 5 rbp,
6 rsi, 7 rdi, 8..15 r8..r15. -/
abbrev Gpr := Nat

inductive MemOp where
  | base (g : Gpr) (disp : Int)
  | rip (off : Nat)               -- rodata + off
  deriving Repr, DecidableEq

/-- Source operand of a vector instruction. -/
inductive Src where
  | reg (n : Nat)
  | mem (m : MemOp)
  | bcst (m : MemOp)              -- `qword bcst [..]`: one word broadcast to all lanes
  deriving Repr, DecidableEq

inductive Cond where
  | e | ne | b | a
  deriving Repr, DecidableEq

inductive Instr where
  /-- vmovdqu/vmovdqa/vmovdqa64/vmovdqu64 register ← source, `lanes` wide;
  with `mask = some k`, lanes whose bit in mask register `k` is clear keep
  their value (merge masking) -/
  | vmov (lanes : Nat) (dst : Nat) (src : Src) (mask : Option Nat)
  | vstore (lanes : Nat) (dst : MemOp) (src : Nat)
  | vpxor (lanes : Nat) (d a : Nat) (b : Src)
  | vpand (lanes : Nat) (d a : Nat) (b : Src)
  | vpandn (lanes : Nat) (d a : Nat) (b : Src)        -- d = ~a & b
  | vpor (lanes : Nat) (d a : Nat) (b : Src)
  | vpaddq (lanes : Nat) (d a : Nat) (b : Src)
  | vpsllq (lanes : Nat) (d a : Nat) (imm : Nat)
  | vpsrlq (lanes : Nat) (d a : Nat) (imm : Nat)
  | vprolq (lanes : Nat) (d a : Nat) (imm : Nat)
  | vpternlogq (lanes : Nat) (d a : Nat) (b : Src) (imm : Nat)
  | vpshufb (lanes : Nat) (d a : Nat) (ctrl : Src)
  | vpunpcklqdq (lanes : Nat) (d a : Nat) (b : Src)
  | vpunpckhqdq (lanes : Nat) (d a : Nat) (b : Src)
  | vperm2i128 (d a : Nat) (b : Src) (imm : Nat)
  | vshufi64x2 (lanes : Nat) (d a : Nat) (b : Src) (imm : Nat)
  | vpermt2q (lanes : Nat) (d idx : Nat) (b : Src)
  | kmovw (k : Nat) (m : MemOp)
  | vzeroupper
  -- general registers
  | mov (d : Gpr) (s : Gpr)
  | movi (d : Gpr) (imm : Int)
  | lea (d : Gpr) (m : MemOp)
  | add (d : Gpr) (imm : Int)
  | sub (d : Gpr) (imm : Int)
  | andi (d : Gpr) (imm : Int)
  | shl (d : Gpr) (imm : Nat)
  | dec (d : Gpr)
  | xorz (d : Gpr)                  -- xor d, d
  | cmpi (a : Gpr) (imm : Int)
  | cmpr (a b : Gpr)
  | test (a b : Gpr)
  | jcc (c : Cond) (target : Nat)   -- target: instruction index
  | jmp (target : Nat)
  | call (target : Nat)
  | ret
  | push (s : Gpr)
  | pop (d : Gpr)
  | storeq (m : MemOp) (s : Gpr)    -- mov qword ptr [m], s
  | loadq (d : Gpr) (m : MemOp)
  | repmovsb
  | tailcall (name : String)        -- jmp to another function (SMALL_TAIL)
  | nop
  deriving Repr, DecidableEq

open LaneOps

/-- The machine state, shared by the x86-64, AArch64 and RISC-V models:
32 vector registers of 8 lanes (ymm/zmm; AArch64 `v` uses 2, RVV uses
VLEN/64), 32 general registers (x86 uses 16; AArch64 x0..x30 and sp = 31;
RISC-V x0..x31), 8 mask registers (AVX-512 `k`), the flags (x86 ZF/CF,
AArch64 N/Z/C/V), the RVV vector length, and memory. -/
structure State (α : Type) where
  v : Vector (Vector α 8) 32   -- vector registers × lanes
  g : Vector Addr 32           -- general registers (as pointers / numbers)
  gd : Vector α 32             -- general registers as data lanes (the scalar Keccak streams)
  k : Vector Nat 8             -- mask registers
  zf : Bool
  cf : Bool
  nf : Bool
  vf : Bool
  vl : Nat
  mem : Region → Int → α       -- memory: region, word index ↦ word
  pc : Nat
  depth : Nat                  -- call depth (ret at depth 0 stops)
  err : Bool
  halted : Bool
  tail : Option String         -- a pending tail call (halted)

variable {α : Type} [LaneOps α]

/-- Region ids. -/
def rInput : Region := 1
def rOutput : Region := 2
def rStack : Region := 3
def rRodata : Region := 4

def State.getV (s : State α) (n : Nat) : List α := (s.v.getD n (Vector.replicate 8 (const 0))).toList
def State.setV (s : State α) (n : Nat) (x : Vector α 8) : State α := { s with v := s.v.setIfInBounds n x }
def State.getG (s : State α) (n : Nat) : Addr := s.g.getD n ⟨0, 0⟩

/-- A general register as a stored word: a number as is, a pointer as (region << 56) | offset. -/
def gprWord (a : Addr) : BitVec 64 :=
  if a.region = 0 then BitVec.ofInt 64 a.off else BitVec.ofNat 64 (a.region.val * 2 ^ 56 + a.off.toNat)

/-- Write a general register (both views). -/
def State.setG (s : State α) (n : Nat) (a : Addr) : State α :=
  { s with g := s.g.setIfInBounds n a, gd := s.gd.setIfInBounds n (const (gprWord a)) }

/-- The data view of a general register. -/
def State.getGD (s : State α) (n : Nat) : α := s.gd.getD n (const 0)
/-- Write a general register as data (its pointer view becomes a plain 0). -/
def State.setGD (s : State α) (n : Nat) (x : α) : State α :=
  { s with g := s.g.setIfInBounds n ⟨0, 0⟩, gd := s.gd.setIfInBounds n x }
def State.fail (s : State α) : State α := { s with err := true, halted := true }

/-- The word at (region, index); the read-only constants come from `rodata`,
not from memory. -/
def State.read (rodata : Array (BitVec 64)) (s : State α) (r : Region) (q : Int) : α :=
  if r = rRodata then (if q ≥ 0 then const (rodata.getD q.toNat 0#64) else const 0) else s.mem r q

/-- Load `n` words at byte offset `a` (8-byte aligned, else `none`). -/
def State.loadWords (rodata : Array (BitVec 64)) (s : State α) (a : Addr) (n : Nat) : Option (List α) :=
  if a.off % 8 = 0 then some ((List.range n).map fun (i : Nat) => s.read rodata a.region (a.off / 8 + Int.ofNat i)) else none

def memStore (m : Region → Int → α) (r : Region) (q : Int) (v : α) : Region → Int → α :=
  fun r' q' => if r' = r ∧ q' = q then v else m r' q'

def memStoreFrom (m : Region → Int → α) (r : Region) (q : Int) : List α → (Region → Int → α)
  | [] => m
  | v :: vs => memStoreFrom (memStore m r q v) r (q + 1) vs

/-- Store words at byte offset `a` (8-byte aligned, never into the constants). -/
def State.storeWords (s : State α) (a : Addr) (vs : List α) : Option (State α) :=
  if a.off % 8 = 0 ∧ a.region ≠ rRodata then some { s with mem := memStoreFrom s.mem a.region (a.off / 8) vs } else none

def memAddr (s : State α) : MemOp → Addr
  | .base g disp => let a := s.getG g; ⟨a.region, a.off + disp⟩
  | .rip off => ⟨rRodata, off⟩

/-- A source operand as `lanes` lane values (`none` on a misaligned load). -/
def readSrc (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) : Src → Option (List α)
  | .reg n => some ((s.getV n).take lanes)
  | .mem m => s.loadWords rodata (memAddr s m) lanes
  | .bcst m => (s.loadWords rodata (memAddr s m) 1).map fun l => List.replicate lanes (l.headD (const 0))

/-- Write a `lanes`-wide result: the lanes above are zeroed. -/
def writeV (s : State α) (n : Nat) (lanes : Nat) (vs : List α) : State α :=
  s.setV n (Vector.ofFn fun i : Fin 8 => if i.val < lanes then vs.getD i.val (const 0) else const 0)

def binop (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) (f : α → α → α) : State α :=
  match readSrc rodata s lanes b with
  | some bs =>
    writeV s d lanes (List.zipWith f ((s.getV a).take lanes) bs)
  | none => s.fail

/-- `vpshufb` on one 128-bit lane (two words `lo`, `hi`) with control bytes
`ctrl` (16 bytes, as two words): byte `i` is zero if the control's bit 7 is
set, else source byte `ctrl & 15`. -/
def shufb128 (lo hi : α) (c0 c1 : BitVec 64) : α × α :=
  let byteOf (w : α) (j : Nat) : α := and (shr w (8 * j)) (const 0xff#64)
  let mk (cw : BitVec 64) : α :=
    (List.range 8).foldl (fun acc i =>
      let m := ((cw >>> (8 * i)) &&& 0xff#64).toNat
      if m &&& 0x80 ≠ 0 then acc
      else
        let src := if (m &&& 15) < 8 then byteOf lo (m &&& 15) else byteOf hi ((m &&& 15) - 8)
        or acc (shl src (8 * i))) (const 0)
  (mk c0, mk c1)

/-- 128-bit lane `j` (two words) of a register value. -/
def lane128 (xs : List α) (j : Nat) : List α := [xs.getD (2 * j) (const 0), xs.getD (2 * j + 1) (const 0)]

def setFlagsSub (s : State α) (a b : Addr) : State α :=
  if a.region = b.region then { s with zf := a.off = b.off, cf := a.off < b.off } else s.fail

/-- Execute one instruction (`rodata` holds the read-only constants). -/
def exec (rodata : Array (BitVec 64)) (i : Instr) (s : State α) : State α :=
  if s.halted then s else
  match i with
  | .vmov lanes dst src mask =>
    match readSrc rodata s lanes src with
    | some vs =>
      let old := (s.getV dst)
      let vs := match mask with
        | none => vs
        | some k =>
          let m := s.k.getD k 0
          (List.range lanes).map fun i => if m.testBit i then vs.getD i (const 0) else old.getD i (const 0)
      { writeV s dst lanes vs with pc := s.pc + 1 }
    | none => s.fail
  | .vstore lanes dst src =>
    match s.storeWords (memAddr s dst) ((s.getV src).take lanes) with
    | some s' => { s' with pc := s.pc + 1 }
    | none => s.fail
  | .vpxor lanes d a b => { binop rodata s lanes d a b xor with pc := s.pc + 1 }
  | .vpand lanes d a b => { binop rodata s lanes d a b and with pc := s.pc + 1 }
  | .vpandn lanes d a b => { binop rodata s lanes d a b (fun x y => and (not x) y) with pc := s.pc + 1 }
  | .vpor lanes d a b => { binop rodata s lanes d a b or with pc := s.pc + 1 }
  | .vpaddq lanes d a b => { binop rodata s lanes d a b add with pc := s.pc + 1 }
  | .vpsllq lanes d a imm =>
    { writeV s d lanes (((s.getV a).take lanes).map fun x => if imm < 64 then shl x imm else const 0) with pc := s.pc + 1 }
  | .vpsrlq lanes d a imm =>
    { writeV s d lanes (((s.getV a).take lanes).map fun x => if imm < 64 then shr x imm else const 0) with pc := s.pc + 1 }
  | .vprolq lanes d a imm =>
    { writeV s d lanes (((s.getV a).take lanes).map fun x => rol x (imm % 64)) with pc := s.pc + 1 }
  | .vpternlogq lanes d a b imm =>
    match readSrc rodata s lanes b with
    | some bs =>
      let ds := (s.getV d).take lanes
      let as_ := (s.getV a).take lanes
      let r := (List.range lanes).map fun i => LaneOps.ternlog imm (ds.getD i (const 0)) (as_.getD i (const 0)) (bs.getD i (const 0))
      { writeV s d lanes r with pc := s.pc + 1 }
    | none => s.fail
  | .vpshufb lanes d a ctrl =>
    match readSrc rodata s lanes ctrl with
    | some cs =>
      let as_ := (s.getV a).take lanes
      let cv := cs.map asConst
      if cv.all Option.isSome then
        let cs' := cv.map fun o => o.getD 0#64
        let r := (List.range (lanes / 2)).foldr (fun j acc =>
          let (lo, hi) := shufb128 (as_.getD (2 * j) (const 0)) (as_.getD (2 * j + 1) (const 0))
                            (cs'.getD (2 * j) 0#64) (cs'.getD (2 * j + 1) 0#64)
          lo :: hi :: acc) []
        { writeV s d lanes r with pc := s.pc + 1 }
      else s.fail
    | none => s.fail
  | .vpunpcklqdq lanes d a b =>
    match readSrc rodata s lanes b with
    | some bs =>
      let as_ := (s.getV a).take lanes
      let r := (List.range (lanes / 2)).foldr (fun j acc => as_.getD (2 * j) (const 0) :: bs.getD (2 * j) (const 0) :: acc) []
      { writeV s d lanes r with pc := s.pc + 1 }
    | none => s.fail
  | .vpunpckhqdq lanes d a b =>
    match readSrc rodata s lanes b with
    | some bs =>
      let as_ := (s.getV a).take lanes
      let r := (List.range (lanes / 2)).foldr (fun j acc => as_.getD (2 * j + 1) (const 0) :: bs.getD (2 * j + 1) (const 0) :: acc) []
      { writeV s d lanes r with pc := s.pc + 1 }
    | none => s.fail
  | .vperm2i128 d a b imm =>
    match readSrc rodata s 4 b with
    | some bs =>
      let as_ := (s.getV a).take 4
      let sel (c : Nat) (z : Bool) : List α :=
        if z then [const 0, const 0] else
        match c % 4 with
        | 0 => lane128 as_ 0 | 1 => lane128 as_ 1 | 2 => lane128 bs 0 | _ => lane128 bs 1
      { writeV s d 4 (sel imm (imm.testBit 3) ++ sel (imm / 16) (imm.testBit 7)) with pc := s.pc + 1 }
    | none => s.fail
  | .vshufi64x2 lanes d a b imm =>
    match readSrc rodata s lanes b with
    | some bs =>
      let as_ := (s.getV a).take lanes
      let n := lanes / 2   -- 128-bit lanes
      let r := (List.range n).foldr (fun j acc =>
        let src := if j < n / 2 then as_ else bs
        let sel := if n = 4 then (imm / 4 ^ j) % 4 else (imm / 2 ^ j) % 2
        lane128 src sel ++ acc) []
      { writeV s d lanes r with pc := s.pc + 1 }
    | none => s.fail
  | .vpermt2q lanes d idx b =>
    match readSrc rodata s lanes b with
    | some bs =>
      let ds := (s.getV d).take lanes
      let is_ := ((s.getV idx).take lanes).map asConst
      if is_.all Option.isSome then
        let r := is_.map fun o =>
          let i := (o.getD 0#64).toNat
          if i % (2 * lanes) < lanes then ds.getD (i % lanes) (const 0) else bs.getD (i % lanes) (const 0)
        { writeV s d lanes r with pc := s.pc + 1 }
      else s.fail
    | none => s.fail
  | .kmovw k m =>
    let a := memAddr s m
    match asConst (s.read rodata a.region (a.off / 8)) with
    | some w => { s with k := s.k.setIfInBounds k (((w >>> (8 * (a.off % 8).toNat)) &&& 0xffff#64).toNat), pc := s.pc + 1 }
    | none => s.fail
  | .vzeroupper => { s with pc := s.pc + 1 }
  | .mov d src => { s.setG d (s.getG src) with pc := s.pc + 1 }
  | .movi d imm => { s.setG d (Addr.num imm) with pc := s.pc + 1 }
  | .lea d m => { s.setG d (memAddr s m) with pc := s.pc + 1 }
  | .add d imm => let a := s.getG d; { s.setG d ⟨a.region, a.off + imm⟩ with pc := s.pc + 1 }
  | .sub d imm =>
    let a := s.getG d
    let s' := s.setG d ⟨a.region, a.off - imm⟩
    -- flags are only meaningful (and only used by the kernels) for plain numbers
    { (if a.region = 0 then setFlagsSub s' a (Addr.num imm) else s') with pc := s.pc + 1 }
  | .andi d imm =>
    -- only used to align the stack pointer: `and rsp, -64`; region bases are 64-byte aligned
    let a := s.getG d
    if imm = -64 then { s.setG d ⟨a.region, a.off - (a.off % 64)⟩ with pc := s.pc + 1 } else s.fail
  | .shl d imm =>
    let a := s.getG d
    if a.region = 0 then { s.setG d ⟨0, a.off * 2 ^ imm⟩ with pc := s.pc + 1 } else s.fail
  | .dec d =>
    let a := s.getG d
    { s.setG d ⟨a.region, a.off - 1⟩ with zf := a.off - 1 = 0, pc := s.pc + 1 }
  | .xorz d => { s.setG d (Addr.num 0) with zf := true, cf := false, pc := s.pc + 1 }
  | .cmpi a imm => { setFlagsSub s (s.getG a) (Addr.num imm) with pc := s.pc + 1 }
  | .cmpr a b => { setFlagsSub s (s.getG a) (s.getG b) with pc := s.pc + 1 }
  | .test a b =>
    let x := s.getG a; let y := s.getG b
    if x.region = 0 ∧ y.region = 0 then
      { s with zf := (BitVec.ofInt 64 x.off &&& BitVec.ofInt 64 y.off) = 0, cf := false, pc := s.pc + 1 }
    else s.fail
  | .jcc c t =>
    let taken := match c with
      | .e => s.zf | .ne => !s.zf | .b => s.cf | .a => !s.cf && !s.zf
    { s with pc := if taken then t else s.pc + 1 }
  | .jmp t => { s with pc := t }
  | .call t =>
    let sp := s.getG 4
    let sp' : Addr := ⟨sp.region, sp.off - 8⟩
    -- the return address is modelled as the instruction index
    match s.storeWords sp' [const (BitVec.ofNat 64 (s.pc + 1))] with
    | some s' => { s'.setG 4 sp' with pc := t, depth := s.depth + 1 }
    | none => s.fail
  | .ret =>
    if s.depth = 0 then { s with halted := true } else
    let sp := s.getG 4
    match s.loadWords rodata sp 1 with
    | some [r] =>
      match asConst r with
      | some ra => { (s.setG 4 ⟨sp.region, sp.off + 8⟩) with pc := ra.toNat, depth := s.depth - 1 }
      | none => s.fail
    | _ => s.fail
  | .push src =>
    let sp := s.getG 4
    let sp' : Addr := ⟨sp.region, sp.off - 8⟩
    let a := s.getG src
    -- general registers are saved as region/offset pairs in a side table: model as a word
    -- tagged by region (region 0 values only, else fail)
    let w := gprWord a
    match s.storeWords sp' [const w] with
    | some s' => { s'.setG 4 sp' with pc := s.pc + 1 }
    | none => s.fail
  | .pop d =>
    let sp := s.getG 4
    match s.loadWords rodata sp 1 with
    | some [w] =>
      match asConst w with
      | some v =>
        let r := (v >>> 56).toNat
        let a : Addr := if r = 0 then ⟨0, v.toInt⟩ else ⟨⟨r % 8, Nat.mod_lt _ (by decide)⟩, ((v &&& 0x00ffffffffffffff#64).toNat : Int)⟩
        { (s.setG d a).setG 4 ⟨sp.region, sp.off + 8⟩ with pc := s.pc + 1 }
      | none => s.fail
    | _ => s.fail
  | .storeq m src =>
    let w := gprWord (s.getG src)
    match s.storeWords (memAddr s m) [const w] with
    | some s' => { s' with pc := s.pc + 1 }
    | none => s.fail
  | .loadq d m =>
    match s.loadWords rodata (memAddr s m) 1 with
    | some [w] =>
      match asConst w with
      | some v =>
        let r := (v >>> 56).toNat
        let a : Addr := if r = 0 then ⟨0, v.toInt⟩ else ⟨⟨r % 8, Nat.mod_lt _ (by decide)⟩, ((v &&& 0x00ffffffffffffff#64).toNat : Int)⟩
        { s.setG d a with pc := s.pc + 1 }
      | none => s.fail
    | _ => s.fail
  | .repmovsb =>
    -- rcx bytes from [rsi] to [rdi]; whole aligned words only
    let n := s.getG 1; let src := s.getG 6; let dst := s.getG 7
    if n.region = 0 ∧ n.off % 8 = 0 ∧ n.off ≥ 0 then
      let words := n.off.toNat / 8
      match s.loadWords rodata src words with
      | some vs =>
        match s.storeWords dst vs with
        | some s' =>
          { ((s'.setG 1 (Addr.num 0)).setG 6 ⟨src.region, src.off + n.off⟩).setG 7 ⟨dst.region, dst.off + n.off⟩ with
              pc := s.pc + 1 }
        | none => s.fail
      | none => s.fail
    else s.fail
  | .tailcall name => { s with halted := true, tail := some name }
  | .nop => { s with pc := s.pc + 1 }

def step (rodata : Array (BitVec 64)) (prog : Array Instr) (s : State α) : State α := exec rodata (prog.getD s.pc .nop) s

/-- Run at most `fuel` instructions, collecting the executed instructions. -/
def run (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → State α → State α × List Instr
  | 0, s => (s, [])
  | n + 1, s =>
    if s.halted then (s, []) else
    let i := prog.getD s.pc .nop
    let (s', tr) := run rodata prog n (exec rodata i s)
    (s', i :: tr)

/-- Execute a recorded instruction sequence. -/
def execTrace (rodata : Array (BitVec 64)) (l : List Instr) (s : State α) : State α := l.foldl (fun s i => exec rodata i s) s

theorem run_eq_execTrace (rodata : Array (BitVec 64)) (prog : Array Instr) (n : Nat) (s : State α) :
    (run rodata prog n s).1 = execTrace rodata (run rodata prog n s).2 s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    split
    · rfl
    · simp only [execTrace, List.foldl_cons]; exact ih _

end Keccaktree.Asm.X86
