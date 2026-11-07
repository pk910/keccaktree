import Keccaktree.Asm.Riscv
import Tools.DiffCases.All
/-! `difftool <set> <vlmax>`: run the Lean models on the differential-test states (stdin) and
print the final states (stdout) in the harness format (lean/difftest/README.md).  The programs are
the test snippets translated by `asm2lean.py` (`Tools.DiffCases.*`). -/
open Keccaktree.Asm Keccaktree.Asm.X86

def W : Nat := 4096

def mixW (seed : UInt64) (r : Nat) (q : Int) : BitVec 64 :=
  let qq : UInt64 := UInt64.ofNat (BitVec.ofInt 64 q).toNat
  let z := seed ^^^ ((UInt64.ofNat r) <<< 56) ^^^ (qq * 0x9E3779B97F4A7C15)
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  BitVec.ofNat 64 (z ^^^ (z >>> 31)).toNat

def hexVal (s : String) : Nat :=
  s.foldl (fun acc c =>
    let d := if c.isDigit then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
    acc * 16 + d) 0

structure Case where
  snip : Nat := 0
  seed : UInt64 := 0
  g : Array (BitVec 64) := Array.replicate 32 0
  v : Array (Array (BitVec 64)) := Array.replicate 32 (Array.replicate 8 0)
  k : Array Nat := Array.replicate 8 0
  zf : Bool := false
  cf : Bool := false
  nf : Bool := false
  vf : Bool := false
  vl : Nat := 0
  mem : List (Nat × Int × BitVec 64) := []

def Case.initMem (c : Case) (r : Region) (q : Int) : BitVec 64 :=
  match c.mem.find? (fun (r', q', _) => r' == r.val && q' == q) with
  | some (_, _, w) => w
  | none => mixW c.seed r.val q

def Case.state (c : Case) (entry : Nat) : State (BitVec 64) :=
  { v := Vector.ofFn fun i : Fin 32 => Vector.ofFn fun l : Fin 8 => (c.v.getD i.val #[]).getD l.val 0
    g := Vector.replicate 32 ⟨0, 0⟩
    gd := Vector.ofFn fun i : Fin 32 => c.g.getD i.val 0
    k := Vector.ofFn fun i : Fin 8 => c.k.getD i.val 0
    zf := c.zf, cf := c.cf, nf := c.nf, vf := c.vf, vl := c.vl
    mem := c.initMem
    pc := entry, depth := 0, err := false, halted := false, tail := none }

def parseLine (c : Case) (ws : List String) : Case :=
  match ws with
  | "C" :: j :: sd :: _ => { snip := j.toNat!, seed := UInt64.ofNat (hexVal sd) }
  | "G" :: i :: w :: _ => { c with g := c.g.set! i.toNat! (BitVec.ofNat 64 (hexVal w)) }
  | "V" :: i :: ls => { c with v := c.v.set! i.toNat! ((ls.map fun w => BitVec.ofNat 64 (hexVal w)).toArray) }
  | "K" :: i :: n :: _ => { c with k := c.k.set! i.toNat! n.toNat! }
  | "F" :: z :: cy :: n :: v :: _ => { c with zf := z == "1", cf := cy == "1", nf := n == "1", vf := v == "1" }
  | "L" :: n :: _ => { c with vl := n.toNat! }
  | "M" :: r :: q :: w :: _ => { c with mem := (r.toNat!, (q.toInt!), BitVec.ofNat 64 (hexVal w)) :: c.mem }
  | _ => c

def hex (w : BitVec 64) : String := String.mk (Nat.toDigits 16 w.toNat)

def which (s : State (BitVec 64)) : Nat :=
  match s.tail with
  | some "kt_back" => 1
  | some "kt_back2" => 2
  | _ => 0

def emit (out : IO.FS.Stream) (n : Nat) (c : Case) (s : State (BitVec 64)) (ng nv nl : Nat) : IO Unit := do
  let mut b : String := s!"C {n}\nX {if s.err then 1 else 0} {if s.halted then 1 else 0} {s.pc}\nW {which s}\n"
  for i in [0:ng] do b := b ++ s!"G {i} {hex (s.gd.getD i 0)}\n"
  b := b ++ s!"F {if s.zf then 1 else 0} {if s.cf then 1 else 0} {if s.nf then 1 else 0} {if s.vf then 1 else 0}\nL {s.vl}\n"
  for i in [0:nv] do
    let lanes := (List.range nl).map fun l => hex ((s.v.getD i (Vector.replicate 8 0)).getD l 0)
    b := b ++ s!"V {i} {" ".intercalate lanes}\n"
  for i in [0:8] do b := b ++ s!"K {i} {s.k.getD i 0}\n"
  for r in [1:4] do
    let rr : Region := ⟨r % 8, Nat.mod_lt _ (by decide)⟩
    for q in [0:W] do
      let w := s.mem rr q
      if w != c.initMem rr q then b := b ++ s!"M {r} {q} {hex w}\n"
  b := b ++ "E\n"
  out.putStr b

def runCase (set : String) (vlmax : Nat) (c : Case) : Option (State (BitVec 64)) :=
  match Tools.DiffCases.find set with
  | some (.x86 prog rodata entries) =>
    some (X86.run rodata prog 64 (c.state (entries.getD c.snip 0))).1
  | some (.arm prog rodata entries) =>
    some (Arm.run rodata prog 64 (c.state (entries.getD c.snip 0))).1
  | some (.riscv prog rodata entries) =>
    some (Riscv.run vlmax rodata prog 64 (c.state (entries.getD c.snip 0))).1
  | none => none

def main (args : List String) : IO UInt32 := do
  let set := args.getD 0 ""
  let vlmax := (args.getD 1 "0").toNat!
  let (ng, nv, nl) := match set.take 3 with
    | "x86" => (16, 32, 8) | "arm" => (32, 32, 2) | _ => (32, 32, 8)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut c : Case := {}
  let mut n := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let ws := ((String.mk (line.toList.filter fun ch => ch != '\n' && ch != '\r')).splitOn " ").filter (· ≠ "")
    if ws.head? == some "E" then
      match runCase set vlmax c with
      | some s => emit stdout n c s ng nv nl
      | none => IO.eprintln s!"unknown set {set}"; return 1
      n := n + 1
    else
      c := parseLine c ws
  return 0
