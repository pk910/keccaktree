import Keccaktree.Asm.Machine
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
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
  | e | ne | b | a | ae | be
  deriving Repr, DecidableEq

/-- Source operand of a scalar (general-register) instruction. -/
inductive GSrc where
  | reg (g : Nat)
  | mem (m : MemOp)
  | imm (i : Int)
  deriving Repr, DecidableEq

inductive AluOp where
  | xor | and | or | add
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
  | vpsllvq (lanes : Nat) (d a : Nat) (b : Src)       -- per-lane shift counts (constants)
  | vpsrlvq (lanes : Nat) (d a : Nat) (b : Src)
  | vpternlogq (lanes : Nat) (d a : Nat) (b : Src) (imm : Nat)
  | vpshufb (lanes : Nat) (d a : Nat) (ctrl : Src)
  | vpshufd (lanes : Nat) (d a : Nat) (imm : Nat)     -- only whole-qword selections
  | vpblendd (lanes : Nat) (d a : Nat) (b : Src) (imm : Nat)  -- only whole-qword blends
  | vpalignr (lanes : Nat) (d a : Nat) (b : Src) (imm : Nat)  -- only multiples of 8 bytes
  | vpunpcklqdq (lanes : Nat) (d a : Nat) (b : Src)
  | vpunpckhqdq (lanes : Nat) (d a : Nat) (b : Src)
  | vperm2i128 (d a : Nat) (b : Src) (imm : Nat)
  | vinserti128 (d a : Nat) (b : Src) (imm : Nat)
  | vextracti128 (m : MemOp) (a : Nat) (imm : Nat)
  | vshufi64x2 (lanes : Nat) (d a : Nat) (b : Src) (imm : Nat)
  | vpermt2q (lanes : Nat) (d idx : Nat) (b : Src)
  | kmovw (k : Nat) (m : MemOp)
  | vzeroupper
  -- general registers: words in `gd`; a pointer or count is a constant word in the `gprWord`
  -- encoding, decoded (`gx`) where an instruction needs it
  | mov (d : Gpr) (s : Gpr)
  | xchg (a b : Gpr)
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
  | cmpm (m : MemOp) (b : Gpr)      -- cmp qword ptr [m], b
  | cmprm (a : Gpr) (m : MemOp)     -- cmp a, qword ptr [m]
  | test (a b : Gpr)
  | bt (a b : Gpr)                  -- cf := bit b of a
  | btc (a : Gpr) (imm : Nat)       -- complement bit imm of a, cf := its old value
  | alu (op : AluOp) (d : Gpr) (b : GSrc)   -- d := d op b (data; flags not modelled)
  | andn (d a : Gpr) (b : GSrc)     -- d := ~a & b
  | rorx (d : Gpr) (b : GSrc) (imm : Nat)
  | xorm (m : MemOp) (s : Gpr)      -- xor qword ptr [m], s
  | storeqi (m : MemOp) (imm : Int) -- mov qword ptr [m], imm
  | addm (m : MemOp) (imm : Int)    -- add qword ptr [m], imm
  | decm (m : MemOp)                -- dec qword ptr [m] (a counter)
  | jcc (c : Cond) (target : Nat)   -- target: instruction index
  | jmp (target : Nat)
  | jcct (c : Cond) (name : String)   -- conditional tail call (`jcc` to another function)
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

/-- A word as a register value: a number as is, a pointer as (region << 56) | offset. -/
def wordGpr (v : BitVec 64) : Addr :=
  let r := (v >>> 56).toNat
  if r = 0 then ⟨0, v.toInt⟩ else ⟨⟨r % 8, Nat.mod_lt _ (by decide)⟩, ((v &&& 0x00ffffffffffffff#64).toNat : Int)⟩

/-- The general registers live in `gd`; a pointer or count is a constant word
in the `gprWord` encoding.  `gx` decodes it; it is `none` for a non-constant
(symbolic) word, and every instruction that needs it fails then. -/
def gx (s : State α) (n : Nat) : Option Addr := (asConst (s.getGD n)).map wordGpr
def setX (s : State α) (n : Nat) (a : Addr) : State α := s.setGD n (const (gprWord a))
def withX (s : State α) (n : Nat) (k : Addr → State α) : State α :=
  match gx s n with
  | some a => k a
  | none => s.fail

def memAddr? (s : State α) : MemOp → Option Addr
  | .base g disp => (gx s g).map fun a => ⟨a.region, a.off + disp⟩
  | .rip off => some ⟨rRodata, off⟩

def withMem (s : State α) (m : MemOp) (k : Addr → State α) : State α :=
  match memAddr? s m with
  | some a => k a
  | none => s.fail

/-- A source operand as `lanes` lane values (`none` on a misaligned or undecodable load). -/
def readSrc (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) : Src → Option (List α)
  | .reg n => some ((s.getV n).take lanes)
  | .mem m => (memAddr? s m).bind fun a => s.loadWords rodata a lanes
  | .bcst m => ((memAddr? s m).bind fun a => s.loadWords rodata a 1).map fun l => List.replicate lanes (l.headD (const 0))

def withSrc (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) (b : Src) (k : List α → State α) : State α :=
  match readSrc rodata s lanes b with
  | some bs => k bs
  | none => s.fail

def withLoad (rodata : Array (BitVec 64)) (s : State α) (a : Addr) (n : Nat) (k : List α → State α) : State α :=
  match s.loadWords rodata a n with
  | some ws => k ws
  | none => s.fail

def withStore (s : State α) (a : Addr) (vs : List α) (k : State α → State α) : State α :=
  match s.storeWords a vs with
  | some s' => k s'
  | none => s.fail

/-- A scalar source operand. -/
def readG (rodata : Array (BitVec 64)) (s : State α) (b : GSrc) (k : α → State α) : State α :=
  match b with
  | .reg g => k (s.getGD g)
  | .imm i => k (const (BitVec.ofInt 64 i))
  | .mem m => withMem s m fun a => withLoad rodata s a 1 fun ws => k (ws.headD (const 0))

def next (s : State α) : State α := { s with pc := s.pc + 1 }

/-- Write a `lanes`-wide result: the lanes above are zeroed. -/
def writeV (s : State α) (n : Nat) (lanes : Nat) (vs : List α) : State α :=
  s.setV n (Vector.ofFn fun i : Fin 8 => if i.val < lanes then vs.getD i.val (const 0) else const 0)

def binop (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) (f : α → α → α) : State α :=
  withSrc rodata s lanes b fun bs => next (writeV s d lanes (List.zipWith f ((s.getV a).take lanes) bs))

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

/-- `vpshufd`: the source qword of result qword `m` (per 128-bit lane), if the
two dword selectors of `imm` pick a whole qword. -/
def qwordSel (imm m : Nat) : Option Nat :=
  let a := (imm / 4 ^ (2 * m)) % 4
  let b := (imm / 4 ^ (2 * m + 1)) % 4
  if a % 2 = 0 ∧ b = a + 1 then some (a / 2) else none

/-- The data-lane ALU operations. -/
def aluOp : AluOp → α → α → α
  | .xor => xor
  | .and => and
  | .or => or
  | .add => add

/-- The word after `vpshufd`/`vpblendd`/`vpalignr` selections: `some` per lane or fail. -/
def allSome (l : List (Option α)) : Option (List α) :=
  if l.all Option.isSome then some (l.map fun o => o.getD (const 0)) else none

/-- `rep movsb` after decoding rcx, rsi, rdi: rcx bytes from [rsi] to [rdi]; whole aligned words only. -/
def repBody (rodata : Array (BitVec 64)) (s : State α) (n src dst : Addr) : State α :=
  if n.region = 0 ∧ n.off % 8 = 0 ∧ n.off ≥ 0 then
    withLoad rodata s src (n.off.toNat / 8) fun vs => withStore s dst vs fun s' =>
      next (setX (setX (setX s' 1 (Addr.num 0)) 6 ⟨src.region, src.off + n.off⟩) 7 ⟨dst.region, dst.off + n.off⟩)
  else s.fail

def condHolds (s : State α) : Cond → Bool
  | .e => s.zf | .ne => !s.zf | .b => s.cf | .a => !s.cf && !s.zf | .ae => !s.cf | .be => s.cf || s.zf

/-- Execute one instruction (`rodata` holds the read-only constants). -/
def exec (rodata : Array (BitVec 64)) (i : Instr) (s : State α) : State α :=
  if s.halted then s else
  match i with
  | .vmov lanes dst src mask => withSrc rodata s lanes src fun vs =>
    let old := (s.getV dst)
    let vs := match mask with
      | none => vs
      | some k =>
        let m := s.k.getD k 0
        (List.range lanes).map fun i => if m.testBit i then vs.getD i (const 0) else old.getD i (const 0)
    next (writeV s dst lanes vs)
  | .vstore lanes dst src => withMem s dst fun a => withStore s a ((s.getV src).take lanes) next
  | .vpxor lanes d a b => binop rodata s lanes d a b xor
  | .vpand lanes d a b => binop rodata s lanes d a b and
  | .vpandn lanes d a b => binop rodata s lanes d a b (fun x y => and (not x) y)
  | .vpor lanes d a b => binop rodata s lanes d a b or
  | .vpaddq lanes d a b => binop rodata s lanes d a b add
  | .vpsllq lanes d a imm =>
    next (writeV s d lanes (((s.getV a).take lanes).map fun x => if imm < 64 then shl x imm else const 0))
  | .vpsrlq lanes d a imm =>
    next (writeV s d lanes (((s.getV a).take lanes).map fun x => if imm < 64 then shr x imm else const 0))
  | .vprolq lanes d a imm =>
    next (writeV s d lanes (((s.getV a).take lanes).map fun x => rol x (imm % 64)))
  | .vpsllvq lanes d a b => withSrc rodata s lanes b fun bs =>
    let cv := bs.map asConst
    if cv.all Option.isSome then
      let cs := cv.map fun o => (o.getD 0#64).toNat
      next (writeV s d lanes ((List.range lanes).map fun i =>
        let n := cs.getD i 64
        if n < 64 then shl ((s.getV a).getD i (const 0)) n else const 0))
    else s.fail
  | .vpsrlvq lanes d a b => withSrc rodata s lanes b fun bs =>
    let cv := bs.map asConst
    if cv.all Option.isSome then
      let cs := cv.map fun o => (o.getD 0#64).toNat
      next (writeV s d lanes ((List.range lanes).map fun i =>
        let n := cs.getD i 64
        if n < 64 then shr ((s.getV a).getD i (const 0)) n else const 0))
    else s.fail
  | .vpternlogq lanes d a b imm => withSrc rodata s lanes b fun bs =>
    let ds := (s.getV d).take lanes
    let as_ := (s.getV a).take lanes
    next (writeV s d lanes ((List.range lanes).map fun i =>
      LaneOps.ternlog imm (ds.getD i (const 0)) (as_.getD i (const 0)) (bs.getD i (const 0))))
  | .vpshufb lanes d a ctrl => withSrc rodata s lanes ctrl fun cs =>
    let as_ := (s.getV a).take lanes
    let cv := cs.map asConst
    if cv.all Option.isSome then
      let cs' := cv.map fun o => o.getD 0#64
      let r := (List.range (lanes / 2)).foldr (fun j acc =>
        let (lo, hi) := shufb128 (as_.getD (2 * j) (const 0)) (as_.getD (2 * j + 1) (const 0))
                          (cs'.getD (2 * j) 0#64) (cs'.getD (2 * j + 1) 0#64)
        lo :: hi :: acc) []
      next (writeV s d lanes r)
    else s.fail
  | .vpshufd lanes d a imm =>
    let as_ := (s.getV a).take lanes
    match allSome ((List.range lanes).map fun i =>
        (qwordSel imm (i % 2)).map fun q => as_.getD (2 * (i / 2) + q) (const 0)) with
    | some r => next (writeV s d lanes r)
    | none => s.fail
  | .vpblendd lanes d a b imm => withSrc rodata s lanes b fun bs =>
    let as_ := (s.getV a).take lanes
    match allSome ((List.range lanes).map fun i =>
        if imm.testBit (2 * i) = imm.testBit (2 * i + 1) then
          some (if imm.testBit (2 * i) then bs.getD i (const 0) else as_.getD i (const 0))
        else none) with
    | some r => next (writeV s d lanes r)
    | none => s.fail
  | .vpalignr lanes d a b imm => withSrc rodata s lanes b fun bs =>
    let as_ := (s.getV a).take lanes
    if imm % 8 = 0 ∧ imm ≤ 32 then
      let r := (List.range (lanes / 2)).foldr (fun j acc =>
        let ws := lane128 bs j ++ lane128 as_ j ++ [const 0, const 0]
        ws.getD (imm / 8) (const 0) :: ws.getD (imm / 8 + 1) (const 0) :: acc) []
      next (writeV s d lanes r)
    else s.fail
  | .vpunpcklqdq lanes d a b => withSrc rodata s lanes b fun bs =>
    let as_ := (s.getV a).take lanes
    let r := (List.range (lanes / 2)).foldr (fun j acc => as_.getD (2 * j) (const 0) :: bs.getD (2 * j) (const 0) :: acc) []
    next (writeV s d lanes r)
  | .vpunpckhqdq lanes d a b => withSrc rodata s lanes b fun bs =>
    let as_ := (s.getV a).take lanes
    let r := (List.range (lanes / 2)).foldr (fun j acc => as_.getD (2 * j + 1) (const 0) :: bs.getD (2 * j + 1) (const 0) :: acc) []
    next (writeV s d lanes r)
  | .vperm2i128 d a b imm => withSrc rodata s 4 b fun bs =>
    let as_ := (s.getV a).take 4
    let sel (c : Nat) (z : Bool) : List α :=
      if z then [const 0, const 0] else
      match c % 4 with
      | 0 => lane128 as_ 0 | 1 => lane128 as_ 1 | 2 => lane128 bs 0 | _ => lane128 bs 1
    next (writeV s d 4 (sel imm (imm.testBit 3) ++ sel (imm / 16) (imm.testBit 7)))
  | .vinserti128 d a b imm => withSrc rodata s 2 b fun bs =>
    let as_ := (s.getV a).take 4
    next (writeV s d 4 (if imm % 2 = 0 then bs ++ lane128 as_ 1 else lane128 as_ 0 ++ bs))
  | .vextracti128 m a imm => withMem s m fun ad =>
    withStore s ad (lane128 ((s.getV a).take 4) (imm % 2)) next
  | .vshufi64x2 lanes d a b imm => withSrc rodata s lanes b fun bs =>
    let as_ := (s.getV a).take lanes
    let n := lanes / 2   -- 128-bit lanes
    let r := (List.range n).foldr (fun j acc =>
      let src := if j < n / 2 then as_ else bs
      let sel := if n = 4 then (imm / 4 ^ j) % 4 else (imm / 2 ^ j) % 2
      lane128 src sel ++ acc) []
    next (writeV s d lanes r)
  | .vpermt2q lanes d idx b => withSrc rodata s lanes b fun bs =>
    let ds := (s.getV d).take lanes
    let is_ := ((s.getV idx).take lanes).map asConst
    if is_.all Option.isSome then
      let r := is_.map fun o =>
        let i := (o.getD 0#64).toNat
        if i % (2 * lanes) < lanes then ds.getD (i % lanes) (const 0) else bs.getD (i % lanes) (const 0)
      next (writeV s d lanes r)
    else s.fail
  | .kmovw k m => withMem s m fun a =>
    match asConst (s.read rodata a.region (a.off / 8)) with
    | some w => next { s with k := s.k.setIfInBounds k (((w >>> (8 * (a.off % 8).toNat)) &&& 0xffff#64).toNat) }
    | none => s.fail
  | .vzeroupper => next s
  | .mov d src => next (s.setGD d (s.getGD src))
  | .xchg a b => next ((s.setGD a (s.getGD b)).setGD b (s.getGD a))
  | .movi d imm => next (s.setGD d (const (BitVec.ofInt 64 imm)))
  | .lea d m => withMem s m fun a => next (setX s d a)
  | .add d imm => withX s d fun a => next (setX s d ⟨a.region, a.off + imm⟩)
  | .sub d imm => withX s d fun a =>
    -- flags are only meaningful (and only used by the kernels) for plain numbers
    if a.region = 0 then next (setFlagsSub (setX s d ⟨0, a.off - imm⟩) a (Addr.num imm))
    else next (setX s d ⟨a.region, a.off - imm⟩)
  | .andi d imm => withX s d fun a =>
    -- only used to align the stack pointer: `and rsp, -64`; region bases are 64-byte aligned
    if imm = -64 then next (setX s d ⟨a.region, a.off - (a.off % 64)⟩) else s.fail
  | .shl d imm => withX s d fun a =>
    if a.region = 0 then next (setX s d ⟨0, a.off * 2 ^ imm⟩) else s.fail
  | .dec d => withX s d fun a => next { setX s d ⟨a.region, a.off - 1⟩ with zf := a.off - 1 = 0 }
  | .xorz d => next { setX s d (Addr.num 0) with zf := true, cf := false }
  | .cmpi a imm => withX s a fun x => next (setFlagsSub s x (Addr.num imm))
  | .cmpr a b => withX s a fun x => withX s b fun y => next (setFlagsSub s x y)
  | .cmpm m b => withMem s m fun ad => withLoad rodata s ad 1 fun ws =>
    match asConst (ws.headD (const 0)) with
    | some v => withX s b fun y => next (setFlagsSub s (wordGpr v) y)
    | none => s.fail
  | .cmprm a m => withMem s m fun ad => withLoad rodata s ad 1 fun ws =>
    match asConst (ws.headD (const 0)) with
    | some v => withX s a fun x => next (setFlagsSub s x (wordGpr v))
    | none => s.fail
  | .test a b => withX s a fun x => withX s b fun y =>
    if x.region = 0 ∧ y.region = 0 then
      next { s with zf := (BitVec.ofInt 64 x.off &&& BitVec.ofInt 64 y.off) = 0, cf := false }
    else s.fail
  | .bt a b =>
    match asConst (s.getGD a) with
    | some w => withX s b fun y =>
      if y.region = 0 ∧ y.off ≥ 0 then next { s with cf := w.getLsbD (y.off.toNat % 64) } else s.fail
    | none => s.fail
  | .btc a imm =>
    match asConst (s.getGD a) with
    | some w => next { s.setGD a (const (w ^^^ (1#64 <<< (imm % 64)))) with cf := w.getLsbD (imm % 64) }
    | none => s.fail
  | .alu op d b => readG rodata s b fun y => next (s.setGD d (aluOp op (s.getGD d) y))
  | .andn d a b => readG rodata s b fun y => next (s.setGD d (and (not (s.getGD a)) y))
  | .rorx d b imm => readG rodata s b fun y => next (s.setGD d (rol y ((64 - imm % 64) % 64)))
  | .xorm m src => withMem s m fun a => withLoad rodata s a 1 fun ws =>
    withStore s a [xor (ws.headD (const 0)) (s.getGD src)] next
  | .storeqi m imm => withMem s m fun a => withStore s a [const (BitVec.ofInt 64 imm)] next
  | .addm m imm => withMem s m fun a => withLoad rodata s a 1 fun ws =>
    withStore s a [add (ws.headD (const 0)) (const (BitVec.ofInt 64 imm))] next
  | .decm m => withMem s m fun a => withLoad rodata s a 1 fun ws =>
    match asConst (ws.headD (const 0)) with
    | some v => withStore s a [const (v - 1#64)] fun s' => next { s' with zf := v - 1#64 = 0#64 }
    | none => s.fail
  | .jcc c t => { s with pc := if condHolds s c then t else s.pc + 1 }
  | .jmp t => { s with pc := t }
  | .jcct c name => if condHolds s c then { s with halted := true, tail := some name } else next s
  | .call t => withX s 4 fun sp =>
    let sp' : Addr := ⟨sp.region, sp.off - 8⟩
    -- the return address is modelled as the instruction index
    withStore s sp' [const (BitVec.ofNat 64 (s.pc + 1))] fun s' => { setX s' 4 sp' with pc := t, depth := s.depth + 1 }
  | .ret =>
    if s.depth = 0 then { s with halted := true } else
    withX s 4 fun sp => withLoad rodata s sp 1 fun ws =>
      match asConst (ws.headD (const 0)) with
      | some ra => { setX s 4 ⟨sp.region, sp.off + 8⟩ with pc := ra.toNat, depth := s.depth - 1 }
      | none => s.fail
  | .push src => withX s 4 fun sp =>
    let sp' : Addr := ⟨sp.region, sp.off - 8⟩
    withStore s sp' [s.getGD src] fun s' => next (setX s' 4 sp')
  | .pop d => withX s 4 fun sp => withLoad rodata s sp 1 fun ws =>
    next (setX (s.setGD d (ws.headD (const 0))) 4 ⟨sp.region, sp.off + 8⟩)
  | .storeq m src => withMem s m fun a => withStore s a [s.getGD src] next
  | .loadq d m => withMem s m fun a => withLoad rodata s a 1 fun ws => next (s.setGD d (ws.headD (const 0)))
  | .repmovsb => withX s 1 fun n => withX s 6 fun src => withX s 7 fun dst => repBody rodata s n src dst
  | .tailcall name => { s with halted := true, tail := some name }
  | .nop => next s

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
