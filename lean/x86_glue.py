#!/usr/bin/env python3
"""Emit `Keccaktree/Kernels/<Dir>/All.lean`: the every-count theorem of an x86 kernel (`NormThm`) from its
generated segments (`x86_all.py gen`) and the count steps of its frame (`Asm/X86Frame.lean`).

    x86_glue.py <kernel>

Structure of the proof (names as emitted):
  * `exit_<X>`  : from a state at the start cut of exit segment X (relocated to node `m`) — the run is done;
  * `body_<z>`  : one iteration of the loop body from the loop head (flag variant z) to the loop control;
  * `afterB`    : from the loop control after k+1 iterations, by induction on the remaining nodes;
  * `afterP`    : from the loop guard after the prologue (all counts: literal cases below `M`, then `M ≤ c`);
  * `norm_thm`  : from the entry (count steps of the entry policy, prologue).
"""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import x86_all as X

HERE = os.path.dirname(os.path.abspath(__file__))
BIG = 10 ** 6
SYM = lambda k: f'keccaktree_keccak256_{k}'


class Val:
    """a register value along count steps: Lean expression + Python value (None: symbolic) + a representative
    value deciding the branches of a symbolic path"""
    def __init__(self, lean, py, rep=None):
        self.lean, self.py = lean, py
        self.rep = py if rep is None else rep


def lit(v):
    return f'({v} : Int)' if v >= 0 else f'(({v}) : Int)'


class FrChain:
    """emit a chain of count steps: `have f<i> := ...`"""
    def __init__(self, prog, rodata, name, out, indent):
        self.prog, self.rodata, self.f, self.out, self.ind = prog, rodata, name, out, indent
        self.i = 0
        self.vals = {}     # reg -> Val
        self.zf = self.cf = None
        self.flags_known = False
        self.pc = None
        self.steps = 0

    def cur(self):
        return f'{self.f}{self.i}'

    def emit(self, s):
        self.out.append(' ' * self.ind + s)

    def nxt(self, expr):
        self.i += 1
        self.emit(f'have {self.cur()} := {expr}')
        self.steps += 1

    def mem(self):
        return '(by simp [setVal])'

    def bound(self):
        return 'fr_lo', 'fr_hi'

    def step(self):
        """one count step at self.pc; returns ('ok'|'tail', info)"""
        pc = self.pc
        op, a = X.parse(self.prog[pc])
        hi = f'(by decide +kernel : prog.getD {pc} .nop = {self.prog[pc]})'
        p = self.cur()
        V = self.vals
        if op == 'cmpi':
            v = V[a[0]]
            self.nxt(f'{p}.cmpi {a[0]} ({a[1]}) {v.lean} {hi} {self.mem()} (by fr_lo) (by fr_hi)')
            self.zf_lean = f'{v.lean} = {a[1]}'
            self.zf, self.cf = v.rep == a[1], v.rep < a[1]
            self.flags_known = v.py is not None
            self.pc = pc + 1
        elif op == 'test':
            v = V[a[0]]
            self.nxt(f'{p}.test {a[0]} {v.lean} {hi} {self.mem()} (by fr_lo) (by fr_hi)')
            self.zf, self.cf = v.rep == 0, False
            self.flags_known = v.py is not None
            self.pc = pc + 1
        elif op == 'sub':
            v = V[a[0]]
            self.nxt(f'{p}.sub {a[0]} (by decide) ({a[1]}) {v.lean} {hi} {self.mem()} (by fr_lo) (by fr_hi)')
            self.zf_lean = f'{v.lean} = {a[1]}'
            self.zf, self.cf = v.rep == a[1], v.rep < a[1]
            self.flags_known = v.py is not None
            V[a[0]] = Val(f'({v.lean} - {a[1]})', None if v.py is None else v.py - a[1], v.rep - a[1])
            self.pc = pc + 1
        elif op == 'movi':
            self.nxt(f'{p}.movi {a[0]} (by decide) ({a[1]}) {hi}')
            V[a[0]] = Val(lit(a[1]), a[1])
            self.pc = pc + 1
        elif op == 'mov':
            v = V[a[1]]
            self.nxt(f'{p}.mov {a[0]} {a[1]} (by decide) {v.lean} {hi} {self.mem()}')
            V[a[0]] = v
            self.pc = pc + 1
        elif op == 'xorz':
            self.nxt(f'{p}.xorz {a[0]} (by decide) {hi}')
            V[a[0]] = Val('(0 : Int)', 0)
            self.zf, self.cf = True, False
            self.flags_known = True
            self.pc = pc + 1
        elif op == 'bt':
            w, v = V[a[0]], V[a[1]]
            self.nxt(f'{p}.bt {a[0]} {a[1]} {w.lean} {v.lean} {hi} {self.mem()} {self.mem()} (by fr_lo) (by fr_hi)')
            self.cf = bool((w.rep % 2 ** 64 >> (v.rep % 64)) & 1)
            self.pc = pc + 1
        elif op in ('nop', 'vzeroupper'):
            self.nxt(f'{p}.nop (Or.{"inl" if op == "nop" else "inr"} {hi})')
            self.pc = pc + 1
        elif op == 'jmp':
            self.nxt(f'{p}.jmp {a[0]} {hi}')
            self.pc = a[0]
        elif op == 'jcc':
            taken = self.decide(a[0])
            tgt = a[1] if taken else pc + 1
            self.nxt(f'({p}.jcc .{a[0]} {a[1]} {hi}).pc_congr (pc\' := {tgt}) (by rw [{"if_pos" if taken else "if_neg"} (by fr_cond)])')
            self.pc = tgt
        elif op == 'jcct':
            taken = self.decide(a[0])
            if taken:
                return 'tail', (a[0], a[1], hi)
            self.nxt(f'{p}.jcct_not .{a[0]} "{a[1]}" {hi} (by fr_cond)')
            self.pc = pc + 1
        else:
            raise AssertionError(('not a count step', pc, self.prog[pc]))
        return 'ok', None

    def decide(self, c):
        assert self.zf is not None and self.cf is not None, (self.pc, c, self.zf, self.cf)
        return X.cond(c, self.zf, self.cf)



def parse_inv(path, idx):
    """the conjuncts of `Inv<idx>` in a generated Invs.lean"""
    txt = open(path).read()
    m = re.search(rf'^def Inv{idx} \(env : Nat → BitVec 64\) \(A : Fin \d+ → Spec.State\) : Prop :=\n(.*?)\n\n', txt, re.S | re.M)
    body = m.group(1).strip()
    conj = [c.strip() for c in body.split(' ∧\n')]
    res = []
    for c in conj:
        mm = re.match(r'^env \(memVar rOutput \(Int.ofNat \(4 \* (\d+) \+ (\d+)\)\)\) = \(specQuantity \(A (\d+)\) (\d+)\)\.rotateLeft (\d+)$', c)
        if mm:
            res.append(('out', int(mm.group(1)), int(mm.group(2)), int(mm.group(3)), int(mm.group(4)), int(mm.group(5))))
            continue
        res.append(('other', c))
    return res


def sc_gd(seg_path, idx):
    """the general registers (gd) of the closed state `sc<idx>` in a generated Seg.lean / Slice file"""
    txt = open(seg_path).read()
    m = re.search(rf'^def sc{idx} : State \(BitVec 64\) := (.*)$', txt, re.M)
    gds = re.findall(r'#v\[((?:0x[0-9a-f]+#64, )*0x[0-9a-f]+#64)\]', m.group(1))
    return [int(x.split('#')[0], 16) for x in gds[0].split(', ')]


def ptr_off(word):
    return word & 0x00ffffffffffffff


def inv0_text(name, G, cnt, nodes):
    consts = ', '.join(f'absorbNode_lane{k} _' for n in nodes for k in range(8, 25))
    return f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The input invariant of `{G}` at node `m`, from the message. -/
theorem inv0_{name} (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat) (hin : ∀ q, S.mem rInput q = input q) :
    {G}.Inv0 (fun i => envOf S ((rho m).var i)) (fun n => absorbNode (nodeWords input (m + n.val))) := by
  have key : ∀ q : Int, envOf S ((rho m).var (memVar rInput q)) = input (q + 8 * (m : Int)) := by
    intro q; rw [rho_var_in, envOf_mem, hin]
  refine ⟨{', '.join(['?_'] * (8 * len(nodes)))}, {consts}⟩
  all_goals
    show envOf S ((rho m).var (memVar rInput _)) = _
    rw [key]
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, nodeWords, rotl0]
    congr 1
    simp only [Int.ofNat_eq_coe]
    omega

"""


def digest_text(name, G, Kx, cnt, nodes, outs, mid_round=None):
    """digests of `nodes` (plan node indices) from `G.Inv<Kx>`; `mid_round`: the plan starts at that round
    (`aat` with an offset), else at round 0"""
    idx = {}
    for j, o in enumerate(outs):
        if o[0] == 'out':
            idx[(o[1], o[2])] = (j, o[3], o[4], o[5])
    for n in nodes:
        for ww in range(4):
            j, an, kind, rot = idx[(n, ww)]
            assert an == n and kind == ww and rot == 0, (n, ww, idx[(n, ww)])
    names = ', '.join(f'h{j}' for j in range(len(outs)))
    b0 = nodes[0]
    hyp = (f"(X A : Fin {cnt} → Spec.State) (hX : ∀ n : Fin {cnt}, X n = absorbNode (nodeWords input (m + n.val)))\n"
           f"    (hA : ∀ n : Fin {cnt}, n.val < {nodes[-1] + 1} → {nodes[0]} ≤ n.val → A n = Spec.rounds {mid_round} (X n))") if mid_round is not None else \
          (f"(A : Fin {cnt} → Spec.State) (hX : ∀ n : Fin {cnt}, A n = absorbNode (nodeWords input (m + n.val)))")
    t = f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The digests at the end of `{G}`. -/
theorem digest_{name} (input : Int → BitVec 64) (T : State (BitVec 64)) (m : Nat) {hyp}
    (h : {G}.Inv{Kx} (fun i => envOf T ((rho m).var i)) ({G}.AAt A {Kx})) :
    ∀ n, n < {len(nodes)} → Digest input T (m + {b0} + n) := by
  obtain ⟨{names}⟩ := h
  have key : ∀ n w : Nat, envOf T ((rho m).var (memVar rOutput (Int.ofNat (4 * n + w)))) =
      T.mem rOutput (Int.ofNat (4 * (m + n) + w)) := by
    intro n w; rw [rho_var_out, envOf_mem]; congr 1; simp only [Int.ofNat_eq_coe]; omega
  intro n hn
"""
    for i, n in enumerate(nodes):
        aat = (f"{G}.aat_{n} X A (hA _ (by decide) (by decide))") if mid_round is not None else f"{G}.aat_{n} A"
        Xn = 'X' if mid_round is not None else 'A'
        t += f"""  by_cases e{i} : n = {i}
  · subst e{i}
    show Digest input T (m + {n})
    have hr : {G}.AAt A {Kx} ⟨{n}, by decide⟩ = Spec.rounds 24 ({Xn} ⟨{n}, by decide⟩) := {aat}
    have hw : ∀ w : Nat, w < 4 → T.mem rOutput (Int.ofNat (4 * (m + {n}) + w)) =
        L ({G}.AAt A {Kx} ⟨{n}, by decide⟩) w := by
      intro w hw
      rw [← key {n} w]
      rcases w with _ | _ | _ | _ | w
""" + ''.join(f"""      · have := h{idx[(n, ww)][0]}; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
          Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
""" for ww in range(4)) + f"""      · omega
    intro w i hw' hi
    rw [hw w hw', hr, hX, absorbNode_keccak, squeezeByte_eq]
    have e1 : (8 * w + i) / 8 = w := by omega
    have e2 : (8 * w + i) % 8 = i := by omega
    rw [e1, e2]
    simp only [Spec.keccakF, Fin.val_mk]
"""
    t += "  omega\n\n"
    return t


def main():
    kernel = sys.argv[1]
    A = json.load(open(os.path.join(HERE, f'plans/{kernel}_all.json')))
    prog, entry, rodata = X.load_prog(kernel)
    N, d = A['N'], A['dir']
    segs = A['segments']
    exits = A['exits']
    used = set(ex['term'][1] for ex in exits if ex['term'][0] != 'ret')
    # the entry policy's conditional tail calls
    for i_, ins in enumerate(prog):
        op_, a_ = X.parse(ins)
        if op_ in ('jcct', 'tailcall'):
            used.add(a_[-1])
    shape = open(os.path.join(HERE, 'Keccaktree/Asm/LibTable.lean')).read()
    m_ = re.search(r'\(sym "' + kernel + r'", (\d+), \[(.*?)\]\)', shape)
    rank = int(m_.group(1))
    targets = [SYM(t) for t in re.findall(r'sym "(\w+)"', m_.group(2))]
    assert set(targets) == used, (targets, used)
    kdir = os.path.join(HERE, f'Keccaktree/Kernels/{d}')
    gen = lambda n: f'Gen{n}'
    ba_names = sorted(n for n in segs if n.startswith('Ba'))
    p_names = sorted(n for n in segs if n.startswith('P'))
    nslices = {n: segs[n]['slices'] for n in segs}
    K = lambda n: nslices[n]
    exnames = [ex['name'] for ex in exits]
    L = []
    w = L.append
    w(''.join(f'import Keccaktree.Kernels.{d}.Gen{n}.Seg\n' for n in sorted(segs)))
    w(f"""import Keccaktree.Asm.X86Kernel
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! GENERATED by lean/x86_glue.py; do not edit.
# `{SYM(kernel)}` on any number of nodes

From the generated segments (prologue `P*`, loop body `Ba*` + `Bb`, exits `X*`) and the frame's count
steps (`Fr`): `norm_thm`, the kernel's `LibX86.NormThm` (every count, from a fresh call). -/
namespace Keccaktree.Kernels.{d}.All
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.X86K Keccaktree.Asm.LibX86 Keccaktree.Proof Keccak
open Keccaktree.Kernels.{d} (prog rodata)

/-- The kernels it may hand over to. -/
def targets : List String := {json.dumps(targets)}

macro "fr_lo" : tactic => `(tactic| first | decide | omega)
macro "fr_hi" : tactic => `(tactic| first | decide | (rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; omega))
macro "fr_eq" : tactic => `(tactic| first | decide +kernel | (rw [decide_eq_true (by omega)]; decide +kernel)
  | (rw [decide_eq_false (by omega)]; decide +kernel))
macro "wok_in" : tactic => `(tactic| (intro q; rfl))
macro "wok_out" : tactic => `(tactic| (intro q hq; first | rfl | (simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff,
  decide_eq_false_iff_not]; omega) | (simp; omega)))

abbrev DoneK := Done rodata prog targets
""")
    # ------------------------------------------------------------------ exits
    XM = 0
    for ex in exits:
        nm = ex['name']; G = gen(nm); seg = segs[nm]
        kx = K(nm)
        segp = os.path.join(kdir, G, 'Seg.lean')
        gd0 = sc_gd(os.path.join(kdir, G, 'Slice0.lean'), 0)
        rem0 = ex['vals'].get('2')
        b0 = ex['src']['count'] - rem0 if rem0 is not None else 0
        nodes = seg['nodes']
        h = len(nodes)
        if nodes:
            assert nodes[0] == b0 and nodes == list(range(b0, b0 + h)), (nm, nodes, b0)
            outsx = parse_inv(os.path.join(kdir, G, 'Invs.lean'), kx)
            w(inv0_text(nm, G, seg['count'], nodes))
            w(digest_text(nm, G, kx, seg['count'], nodes, outsx))
            data = f"""  have sr := {G}.seg_run (rho m) (rho_ok m) (rho_within m hmb) U hcut hI.ok
  have dx := {G}.seg_data (rho m) (rho_ok m) (rho_within m hmb) U hcut hI.ok _ (inv0_{nm} input U m hI.inp)
  rw [← sr.1] at dx
  have dg := digest_{nm} input _ m _ (fun _ => rfl) dx
  have hI' := hI.seg' {G}.facts m {b0} (by omega) hmb hcut (by wok_in) (by wok_out)
  have hdig : ∀ n, n < done + {h} → Digest input (X86.isa.run rodata prog {G}.facts.len U) (off + n) := by
    intro n hn
    by_cases hn' : n < done
    · exact hI'.dig n hn'
    · have := dg (n - done) (by omega)
      rw [show m + {b0} + (n - done) = off + n by omega] at this
      exact this
"""
        else:
            data = f"""  have hI' := hI.seg {G}.facts m (by omega) hmb hcut (by wok_in) (by wok_out)
  have hdig : ∀ n, n < done + 0 → Digest input (X86.isa.run rodata prog {G}.facts.len U) (off + n) :=
    fun n hn => hI'.dig n (by omega)
"""
        if ex['term'][0] == 'ret':
            w(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- Exit `{nm}` (from instruction {ex['pc']}): its segment, then `ret` at depth 0; every node is done. -/
theorem exit_{nm} (off c : Nat) (input : Int → BitVec 64) (S0 U : State (BitVec 64)) (done m : Nat)
    (hcut : relocState (rho m) (cutOf {G}.facts.ctl0 {G}.facts.sc0) = cutOf {G}.facts.ctl0 U)
    (hI : Inv off c input S0 U done) (hmd : off + done = m + {b0}) (hb : 64 * (off + c) ≤ 2 ^ 54) (hc : done + {h} = c) :
    DoneK off c input S0 U ({G}.facts.len + 1) := by
  have hmb : 64 * m ≤ 2 ^ 54 := by omega
  obtain ⟨hok, hcutK⟩ := {G}.facts.run (rho m) (rho_ok m) (rho_within m hmb) U hcut hI.ok
{data}  have fK := cut_fields _ _ _ _ hcutK
  have hr := run_ret0 rodata prog _ hok.2.1 (by rw [fK.2.2.2.2.2.2.2.1]; decide +kernel)
    (fK.2.2.2.2.2.2.2.2.trans (by decide +kernel))
  have hr2 : X86.isa.run rodata prog ({G}.facts.len + 1) U =
      {{ X86.isa.run rodata prog {G}.facts.len U with halted := true }} := by rw [Isa.run_add, hr]
  apply Done.mono (k := {G}.facts.len + 1 + 0) _ (by omega)
  apply Done.run hr2
  intro n _
  rw [Isa.run_halted _ _ _ _ _ rfl]
  exact ⟨rfl, hok.1, fun q hq => hI'.pre q hq, Or.inl ⟨hok.2.2, fun n hn => hdig n (by omega)⟩⟩

""")
        else:
            kind, name = ex['term']
            gdK = sc_gd(segp, kx)
            r = gdK[2]
            bK = ptr_off(gdK[6]) // 64
            assert ptr_off(gdK[7]) == 32 * bK
            assert bK - b0 == h, (nm, bK, b0, h)
            sym = name if name.startswith('keccaktree_') else SYM(name)
            if kind == 'tailcall':
                term = f"run_tail rodata prog _ hok.2.1 \"{sym}\" (by rw [fK.2.2.2.2.2.2.2.1]; decide +kernel)"
            else:
                term = (f"run_jcct rodata prog _ hok.2.1 _ \"{sym}\" (by rw [fK.2.2.2.2.2.2.2.1]; decide +kernel) "
                        f"(by rw [fK.2.2.1, fK.2.2.2.1]; decide +kernel)")
            w(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- Exit `{nm}` (from instruction {ex['pc']}): its segment, then the tail call to `{sym}` with {r} nodes. -/
theorem exit_{nm} (off c : Nat) (input : Int → BitVec 64) (S0 U : State (BitVec 64)) (done m : Nat)
    (hcut : relocState (rho m) (cutOf {G}.facts.ctl0 {G}.facts.sc0) = cutOf {G}.facts.ctl0 U)
    (hI : Inv off c input S0 U done) (hmd : off + done = m + {b0}) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (hc : done + {bK - b0} + {r} = c) :
    DoneK off c input S0 U ({G}.facts.len + 1) := by
  have hmb : 64 * m ≤ 2 ^ 54 := by omega
  obtain ⟨hok, hcutK⟩ := {G}.facts.run (rho m) (rho_ok m) (rho_within m hmb) U hcut hI.ok
{data}  have fK := cut_fields _ _ _ _ hcutK
  have hr := {term}
  have hr2 : X86.isa.run rodata prog ({G}.facts.len + 1) U =
      {{ X86.isa.run rodata prog {G}.facts.len U with halted := true, tail := some "{sym}" }} := by rw [Isa.run_add, hr]
  apply Done.mono (k := {G}.facts.len + 1 + 0) _ (by omega)
  apply Done.run hr2
  intro n _
  rw [Isa.run_halted _ _ _ _ _ rfl]
  refine ⟨rfl, hok.1, fun q hq => hI'.pre q hq, Or.inr ⟨"{sym}", done + {bK - b0}, rfl, by decide, by omega,
    fun n hn => hdig n (by omega), ?_⟩⟩
  · have he := handover m {G}.facts.ctlK {G}.facts.scK (X86.isa.run rodata prog {G}.facts.len U) _ input hcutK {r} {bK}
      (by decide +kernel) ⟨rfl, rfl, rfl, rfl, hok.1, rfl, rfl⟩ hI'.inp
    rw [show m + {bK} = off + (done + {bK - b0}) by omega, show {r} = c - (done + {bK - b0}) by omega] at he
    exact ⟨he, by omega⟩

""")
        XM = max(XM, ex['len'] + 1)
    XM += 40
    # ------------------------------------------------------------------ body
    Kb = K('Bb')
    cntB = 2 * N
    outs = parse_inv(os.path.join(kdir, 'GenBb', 'Invs.lean'), Kb)
    plan_ba = json.load(open(os.path.join(HERE, f'plans/{kernel}_{ba_names[0]}.json')))
    rW = plan_ba['rounds'][-1][0]
    w(digest_text('Bb', 'GenBb', Kb, cntB, list(range(N)), outs, mid_round=rW))
    for nm in ba_names:
        G = gen(nm)
        w(inv0_text(nm, G, cntB, list(range(N))))
        w(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One loop iteration** (flag variant `{nm}`): from the loop head at node `off + done`, the body hashes
nodes `done .. done + {N}` and stops before the loop control, the count register unchanged. -/
theorem body_{nm} (off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (done : Nat)
    (hcut : relocState (rho (off + done)) (cutOf {G}.facts.ctl0 {G}.facts.sc0) = cutOf {G}.facts.ctl0 S)
    (hI : Inv off c input S0 S done) (hb : 64 * (off + done + {N}) ≤ 2 ^ 54) :
    relocState (rho (off + done)) (cutOf GenBb.facts.ctlK GenBb.facts.scK) =
      cutOf GenBb.facts.ctlK (X86.isa.run rodata prog ({G}.facts.len + GenBb.facts.len) S) ∧
    Inv off c input S0 (X86.isa.run rodata prog ({G}.facts.len + GenBb.facts.len) S) (done + {N}) ∧
    envOf (X86.isa.run rodata prog ({G}.facts.len + GenBb.facts.len) S) 258 = envOf S 258 := by
  have hmb : 64 * (off + done) ≤ 2 ^ 54 := by omega
  have hρ := rho_ok (off + done)
  have hw := rho_within (off + done) hmb
  obtain ⟨ok1, cut1⟩ := {G}.facts.run _ hρ hw S hcut hI.ok
  have sr1 := {G}.seg_run _ hρ hw S hcut hI.ok
  have da := {G}.seg_data _ hρ hw S hcut hI.ok _ (inv0_{nm} input S (off + done) hI.inp)
  rw [← sr1.1] at da
  have cut2 := seg_chain {G}.facts GenBb.facts _ hρ _ cut1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨ok2, cut3⟩ := GenBb.facts.run _ hρ hw _ cut2 ok1
  have sr2 := GenBb.seg_run _ hρ hw _ cut2 ok1
  have db := GenBb.seg_data _ hρ hw _ cut2 ok1 _ da
  rw [← sr2.1] at db
  have dg := digest_Bb input _ (off + done) _ _ (fun _ => rfl) (fun n => match n with
""" + ''.join(f"""    | ⟨{n}, _⟩ => fun _ _ => {G}.aat_{n} _
""" for n in range(N)) + f"""    | ⟨n + {N}, _⟩ => fun h1 _ => absurd h1 (by simp only [Fin.val_mk]; omega)) db
  have I1 := hI.seg {G}.facts (off + done) (by omega) hmb hcut (by wok_in) (by wok_out)
  have I2 := I1.seg GenBb.facts (off + done) (by omega) hmb cut2 (by wok_in) (by wok_out)
  rw [Isa.run_add]
  refine ⟨cut3, ⟨I2.ok, I2.inp, I2.pre, fun n hn => ?_⟩, ?_⟩
  · by_cases hn' : n < done
    · exact I2.dig n hn'
    · have := dg (n - done) (by omega)
      rw [show off + done + 0 + (n - done) = off + n by omega] at this
      exact this
  · exact (GenBb.facts_rdx _ hρ hw _ cut2 ok1).trans ({G}.facts_rdx _ hρ hw _ hcut hI.ok)

""")
    # ------------------------------------------------------------------ loop control and dispatch
    lens = {}
    for nm in sorted(segs):
        # segment lengths (closed): from the plan (end - start)
        lens[nm] = segs[nm]['end'] - segs[nm]['start']
    for nm in sorted(segs):
        w(f"""theorem len_{nm} : Gen{nm}.facts.len = {lens[nm]} := by decide +kernel
""")
    LBa = lens[ba_names[0]]
    assert all(lens[n] == LBa for n in ba_names)
    LI = 16 + LBa + lens['Bb']
    H, C = A['H'], A['C']
    w(f"""
/-- Steps per loop iteration (control, body). -/
def LI : Nat := {LI}
/-- Steps after the last iteration (dispatch, exit). -/
def XM : Nat := {XM}
""")
    exit_by_key = {(ex['pc'], tuple(sorted((int(k), v) for k, v in ex['vals'].items())), tuple(ex['flags']), ex.get('kset', False)): ex for ex in exits}

    def run_chain(out, ind, fname, vals, pc, zf, cf, stop_pcs, subst=None):
        """emit count steps from `pc` until a non-count instruction; returns (chain, kind, info)"""
        ch = FrChain(prog, rodata, fname, out, ind)
        ch.vals = dict(vals); ch.pc = pc; ch.zf, ch.cf = zf, cf
        while True:
            if ch.pc in stop_pcs:
                return ch, 'stop', ch.pc
            if X.fr_step(prog, rodata, ch.pc, {k: v.rep for k, v in ch.vals.items()}, bool(ch.zf), bool(ch.cf)) is None:
                return ch, 'exit', ch.pc
            kind, info = ch.step()
            if kind == 'tail':
                return ch, 'tail', info
            if subst and ch.i in subst:
                for (expr, litv, reg) in subst[ch.i]:
                    ch.emit(f'have hv{ch.i} : {expr} = {lit(litv)} := by omega')
                    ch.emit(f'rw [hv{ch.i}] at {ch.cur()}')
                    ch.vals[reg] = Val(lit(litv), litv)

    def emit_exit_call(out, ind, ch, prev_cut, prev_m, prev_base, done_expr, Tn, cnt_expr):
        """from the end of a count-step chain at an exit's first instruction: Fr.cut and the exit lemma"""
        key = (ch.pc, tuple(sorted((k, v.py) for k, v in ch.vals.items() if k in (0, 1, 2) and v.py is not None)),
               (bool(ch.zf), bool(ch.cf)))
        ex = None
        for (pc_, vals_, fl_, _ks), e in exit_by_key.items():
            if pc_ == ch.pc and fl_ == key[2] and all(ch.vals.get(k) is not None and ch.vals[k].py == v for k, v in vals_) \
                    and bool(e.get('kset', False)) == bool(cnt_expr):
                ex = e
        assert ex is not None, ('no exit for', key)
        nm = ex['name']; G = gen(nm)
        rem0 = ex['vals'].get('2'); b0 = ex['src']['count'] - rem0
        sig = prev_base - b0
        assert sig >= 0, (prev_base, b0)
        o = lambda t: out.append(' ' * ind + t)
        o(f'have hx := Fr.cut (rho_ok {prev_m}) (rho_ok {sig}) _ {G}.facts.ctl0 _ {G}.facts.sc0')
        o(f'  (PreCut.of_cut _ (rho_ok _) _ _ _ {prev_cut}) {ch.cur()} (by decide +kernel) (by decide +kernel)')
        o(f'  (by fr_eq) (by fr_eq) (by decide +kernel)')
        o(f'rw [rho_add] at hx')
        if ex['term'][0] == 'ret':
            hc = '(by omega)'
        else:
            hc = '(by omega)'
        o(f'have hd := exit_{nm} off c input S0 _ ({done_expr}) _ hx (hI.fr {ch.cur()}) (by omega) hb {hc}')
        o(f'rw [len_{nm}] at hd')
        o(f'exact (Done.run rfl hd).mono (by unfold XM LI; omega)')
        return ex

    def path_from(pc0, y_rdx, stop):
        """count-step path (pcs) from pc0 with rdx = y_rdx, until `stop` (H), a non-count instruction or a tail"""
        ch = FrChain(prog, rodata, 'x', [], 0)
        ch.vals = {2: Val('y', y_rdx)}; ch.pc = pc0
        pcs = []
        while ch.pc != stop and X.fr_step(prog, rodata, ch.pc, {k_: v.rep for k_, v in ch.vals.items()}, bool(ch.zf), bool(ch.cf)) is not None:
            pcs.append(ch.pc)
            k_, _ = ch.step()
            if k_ == 'tail':
                return pcs + ['tail']
        return pcs + [ch.pc]

    def emit_dispatch(ind, f0, E0, delta, yvar, ylo, pc0, prev_m, prev_base, done_expr, on_H, msuf=''):
        """count steps from `f0` (at pc0, rdx = E0 = yvar + delta) to the loop head or an exit, for every value of
        the Nat `yvar` ≥ ylo: literal cases below the uniform bound M, then `M ≤ yvar`"""
        out = []
        oo = lambda t, d=0: out.append(' ' * (ind + d) + t)
        big = path_from(pc0, BIG + delta, H)
        M = ylo
        for y in range(ylo, A['maxc'] + 1):
            if path_from(pc0, y + delta, H) != big:
                M = y + 1
        assert big[-1] == H, big
        if M > ylo:
            oo(f"have hcs : {' ∨ '.join([f'{yvar} = {y}' for y in range(ylo, M)] + [f'{M} ≤ {yvar}'])} := by omega")
            oo(f"rcases hcs with {' | '.join(['hy'] * (M - ylo) + ['hy'])}")
        groups = list(range(ylo, M)) + ['sym']
        for y in groups:
            d0 = 2 if M > ylo else 0
            if M > ylo:
                oo("· -- " + (f"{yvar} = {y}" if y != 'sym' else f"{M} ≤ {yvar}"))
            sub = []
            if y == 'sym':
                vals = {2: Val(E0, None, BIG + delta)}
                ch, kind, info = run_chain(sub, ind + d0, f0 + 'x', vals, pc0, None, None, {H})
            else:
                sub.append(' ' * (ind + d0) + f'have hv : {E0} = {lit(y + delta)} := by omega')
                sub.append(' ' * (ind + d0) + f'rw [hv] at {f0}')
                vals = {2: Val(lit(y + delta), y + delta)}
                ch, kind, info = run_chain(sub, ind + d0, f0 + 'x', vals, pc0, None, None, {H})
            # the chain starts at f0: rename its 0th hypothesis
            sub = [l.replace(f'{f0}x0', f0) for l in sub]
            if ch.i == 0:
                ch.f, ch.i = f0, None
                ch.cur = (lambda nm=f0: nm)
            out.extend(sub)
            if kind == 'stop':
                both = ('Bat' + msuf) in ba_names and ('Baf' + msuf) in ba_names
                if not ch.flags_known and both:
                    oo(f"by_cases hz : {ch.zf_lean}", d0)
                    for nm in ('Bat' + msuf, 'Baf' + msuf):
                        ch.zf = nm.startswith('Bat')
                        hl = []
                        on_H(hl, ind + d0 + 2, ch, nm)
                        hl[0] = ' ' * (ind + d0) + '· ' + hl[0].lstrip()
                        out.extend(hl)
                else:
                    nm = ('Bat' if ch.zf else 'Baf') + msuf
                    if nm not in ba_names:
                        nm = [n_ for n_ in ba_names if n_.endswith(msuf) or not msuf][0]
                    on_H(out, ind + d0, ch, nm)
            elif kind == 'exit':
                emit_exit_call(out, ind + d0, ch, 'hcut', prev_m, prev_base, done_expr, 'T', bool(msuf))
            else:
                raise AssertionError(('dispatch ends in', kind, y))
        return out

    # afterB_step: the loop control, with the continuation as a hypothesis
    L.append(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The loop control after `k + 1` iterations: on to the next iteration (`cont`) or to an exit. -/
theorem afterB_step (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (T : State (BitVec 64)) (hk : {N} * (k + 1) ≤ c)
    (hcut : relocState (rho (off + {N} * k)) (cutOf GenBb.facts.ctlK GenBb.facts.scK) = cutOf GenBb.facts.ctlK T)
    (hI : Inv off c input S0 T ({N} * (k + 1))) (hrdx : T.getGD 2 = BitVec.ofInt 64 ((c : Int) - {N} * (k : Int)))
    (cont : {N} ≤ c - {N} * (k + 1) → ∀ T' : State (BitVec 64),
      relocState (rho (off + {N} * (k + 1))) (cutOf GenBb.facts.ctlK GenBb.facts.scK) = cutOf GenBb.facts.ctlK T' →
      Inv off c input S0 T' ({N} * (k + 1 + 1)) → T'.getGD 2 = BitVec.ofInt 64 ((c : Int) - {N} * ((k + 1 : Nat) : Int)) →
      DoneK off c input S0 T' (LI * (c - {N} * (k + 1 + 1)) + XM)) :
    DoneK off c input S0 T (LI * (c - {N} * (k + 1)) + XM) := by
  have hc55 : (c : Int) < 36028797018963968 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have f0 : Fr rodata prog T 0 T.pc T.zf T.cf [(2, (c : Int) - {N} * (k : Int))] [] :=
    Fr.start T _ ((cut_fields _ _ _ _ hcut).1.trans (by decide +kernel))
      (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; exact hrdx)
      hI.ok.1 hI.ok.2.1 hI.ok.2.2
  have f0 := f0.pc_congr (pc' := {C}) ((cut_fields _ _ _ _ hcut).2.2.2.2.2.2.2.1.trans (by decide +kernel))""")
    def on_H_B(out, ind, ch, nm):
        G = gen(nm)
        e = ch.vals[2].lean
        for t in f"""have hx := Fr.cut (rho_ok (off + {N} * k)) (rho_ok {N}) _ {G}.facts.ctl0 _ {G}.facts.sc0
  (PreCut.of_cut _ (rho_ok _) _ _ _ hcut) {ch.cur()} (by decide +kernel) (by decide +kernel) (by fr_eq) (by fr_eq) (by decide +kernel)
rw [rho_add, show off + {N} * k + {N} = off + {N} * (k + 1) by omega] at hx
obtain ⟨hc', hI', hr'⟩ := body_{nm} off c input S0 _ ({N} * (k + 1)) hx (hI.fr {ch.cur()}) (by omega)
have hd := cont (by omega) _ hc' hI' (by
  rw [← envOf_gdVar _ 2 (by decide), hr', envOf_gdVar _ 2 (by decide), {ch.cur()}.vals (2, {e}) (by simp [setVal])]
  congr 1; push_cast; omega)
rw [len_{nm}, len_Bb] at hd ⊢
exact (Done.run rfl (Done.run rfl hd)).mono (by unfold LI; omega)""".split('\n'):
            out.append(' ' * ind + t)
    L.extend(emit_dispatch(2, 'f0', f'((c : Int) - {N} * (k : Int))', N, f'c - {N} * (k + 1)', 0, C,
                           f'(off + {N} * k)', N, f'{N} * (k + 1)', on_H_B,
                           msuf='m' if any(n_.endswith('m') for n_ in ba_names) else ''))
    L.append('')
    w(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The loop**: from the loop control after `k + 1` iterations (count register `c - {N}k`), every run of
`LI · (c - {N}(k+1)) + XM` steps is an outcome. -/
theorem afterB (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ j k (T : State (BitVec 64)), c - {N} * (k + 1) ≤ j → {N} * (k + 1) ≤ c →
      relocState (rho (off + {N} * k)) (cutOf GenBb.facts.ctlK GenBb.facts.scK) = cutOf GenBb.facts.ctlK T →
      Inv off c input S0 T ({N} * (k + 1)) → T.getGD 2 = BitVec.ofInt 64 ((c : Int) - {N} * (k : Int)) →
      DoneK off c input S0 T (LI * (c - {N} * (k + 1)) + XM) := by
  intro j
  induction j with
  | zero =>
    intro k T hj hk hcut hI hrdx
    exact afterB_step off c input S0 hb k T hk hcut hI hrdx (fun hcont => absurd hcont (by omega))
  | succ j ih =>
    intro k T hj hk hcut hI hrdx
    exact afterB_step off c input S0 hb k T hk hcut hI hrdx (fun hcont T' hcut' hI' hrdx' =>
      ih (k + 1) T' (by omega) (by omega) hcut' hI' hrdx')
""")

    # ------------------------------------------------------------------ after the prologue: the guard
    G_pc = A['G']
    GA = 40
    for pv in p_names:
        GP = gen(pv)
        L.append(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **After the prologue** (`{pv}`): the loop guard, then the loop or an exit. -/
theorem afterP_{pv} (off c : Nat) (input : Int → BitVec 64) (S0 T : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (hcut : relocState (rho off) (cutOf {GP}.facts.ctlK {GP}.facts.scK) = cutOf {GP}.facts.ctlK T)
    (hI : Inv off c input S0 T 0) (hrdx : T.getGD 2 = BitVec.ofInt 64 (c : Int)) :
    DoneK off c input S0 T ({GA} + LI * c + XM) := by
  have hc55 : (c : Int) < 36028797018963968 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have f0 : Fr rodata prog T 0 T.pc T.zf T.cf [(2, (c : Int))] [] :=
    Fr.start T _ ((cut_fields _ _ _ _ hcut).1.trans (by decide +kernel))
      (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; exact hrdx)
      hI.ok.1 hI.ok.2.1 hI.ok.2.2
  have f0 := f0.pc_congr (pc' := {G_pc}) ((cut_fields _ _ _ _ hcut).2.2.2.2.2.2.2.1.trans (by decide +kernel))""")
        def on_H_P(out, ind, ch, nm):
            G = gen(nm)
            e = ch.vals[2].lean
            for t in f"""have hx := Fr.cut (rho_ok off) (rho_ok 0) _ {G}.facts.ctl0 _ {G}.facts.sc0
  (PreCut.of_cut _ (rho_ok _) _ _ _ hcut) {ch.cur()} (by decide +kernel) (by decide +kernel) (by fr_eq) (by fr_eq) (by decide +kernel)
rw [rho_add] at hx
obtain ⟨hc', hI', hr'⟩ := body_{nm} off c input S0 _ 0 hx (hI.fr {ch.cur()}) (by omega)
have hd := afterB off c input S0 hb _ 0 _ (le_refl _) (by omega) (by simpa using hc') (by simpa using hI') (by
  rw [← envOf_gdVar _ 2 (by decide), hr', envOf_gdVar _ 2 (by decide), {ch.cur()}.vals (2, {e}) (by simp [setVal])]
  congr 1; push_cast; omega)
rw [len_{nm}, len_Bb] at hd ⊢
exact (Done.run rfl (Done.run rfl hd)).mono (by unfold LI XM; omega)""".split('\n'):
                out.append(' ' * ind + t)
        L.extend(emit_dispatch(2, 'f0', '(c : Int)', 0, 'c', 0, G_pc, 'off', 0, '0', on_H_P))
        L.append('')
    # ------------------------------------------------------------------ the entry
    ENT = entry
    def policy_path(cv):
        ch = FrChain(prog, rodata, 'x', [], 0)
        ch.vals = {2: Val('c', cv)}; ch.pc = ENT
        pcs = []
        while X.fr_step(prog, rodata, ch.pc, {k: v.py for k, v in ch.vals.items()}, bool(ch.zf), bool(ch.cf)) is not None:
            pcs.append(ch.pc)
            k_, info = ch.step()
            if k_ == 'tail':
                return pcs + ['tail']
        return pcs + [ch.pc]
    bigp = policy_path(BIG)
    assert bigp[-1] == A['P0'], bigp
    Mp = 0
    for cv in range(A['maxc'] + 1):
        if policy_path(cv) != bigp:
            Mp = cv + 1
    PL = max(lens[pv] for pv in p_names)
    SA = GA + PL + 40
    L.append(f"""/-- The step bound of a call on `c` nodes. -/
def steps (off c : Nat) : Nat := {SA} + LI * c + XM

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`{SYM(kernel)}` on any number of nodes**, from a fresh call. -/
theorem norm_thm : NormThm rodata prog {ENT} steps targets := by
  intro off c input S hE hb hpc
  have I0 : Inv off c input S S 0 := ⟨hE.ok, hE.inp, fun _ _ => rfl, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  have hc55 : (c : Int) < 36028797018963968 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hmb : 64 * off ≤ 2 ^ 54 := by omega
  have f0 := (X86K.Fr.entry rodata prog off c input S hE).pc_congr (pc' := {ENT}) hpc""")
    def entry_case(ind, cv):
        out = []
        oo = lambda t: out.append(' ' * ind + t)
        vals = {2: Val('(c : Int)', None, BIG)} if cv == 'sym' else {2: Val(f'((({cv} : Nat)) : Int)', cv)}
        ch, kind, info = run_chain(out, ind, 'f', vals, ENT, None, None, set())
        if cv == 'sym':
            # the flags at P0 for large counts (decided by `fr_eq` from `Mp ≤ c`)
            ch2 = FrChain(prog, rodata, 'x', [], 0); ch2.vals = {2: Val('c', BIG)}; ch2.pc = ENT
            while ch2.pc != A['P0']:
                ch2.step()
            flags = (bool(ch2.zf), bool(ch2.cf)) if ch2.i > 0 else (False, False)
        else:
            flags = (bool(ch.zf), bool(ch.cf)) if ch.i > 0 else (False, False)
        f = ch.cur()
        if kind == 'tail':
            cnd, name, hi = info
            sym = name if name.startswith('keccaktree_') else SYM(name)
            oo(f'have hr := {f}.jcct_taken .{cnd} "{sym}" {hi} (by fr_cond)')
            oo(f'intro n hn')
            oo(f'rw [show n = ({ch.i} + 1) + (n - ({ch.i} + 1)) by omega, Isa.run_add, hr, Isa.run_halted _ _ _ _ _ rfl]')
            oo(f'refine ⟨rfl, {f}.err, fun q _ => by rw [{f}.near.2.2.2.2.2.2.1], Or.inr ⟨"{sym}", 0, rfl, by decide, by omega,')
            oo(f'  fun n hn => absurd hn (Nat.not_lt_zero _), ?_⟩⟩')
            oo(f'simp only [Nat.add_zero, Nat.sub_zero]')
            oo(f'exact ⟨handover_fr hE {f} (by decide) _ ⟨rfl, rfl, rfl, rfl, {f}.err, rfl, rfl⟩, hb⟩')
            return out
        assert kind == 'exit' and ch.pc == A['P0'], (cv, kind, ch.pc)
        pv = 'P' + ('t' if flags[0] else 'f') + ('t' if flags[1] else 'f')
        assert pv in p_names, (pv, p_names)
        GP = gen(pv)
        zfp = '(by fr_eq)' if ch.i > 0 else '(hE.ctrl.2.2.1.trans (by decide +kernel))'
        cfp = '(by fr_eq)' if ch.i > 0 else '(hE.ctrl.2.2.2.1.trans (by decide +kernel))'
        for t in f"""have hx := Fr.cut (rho_ok off) (rho_ok 0) entryCtl {GP}.facts.ctl0 entrySc {GP}.facts.sc0
  (PreCut.entry off c input S hE hb) {f} (by decide +kernel) (by decide +kernel) {zfp} {cfp} (by decide +kernel)
rw [rho_add, Nat.add_zero] at hx
obtain ⟨ok1, cut1⟩ := {GP}.facts.run (rho off) (rho_ok off) (rho_within off hmb) _ hx (I0.fr {f}).ok
have I1 := (I0.fr {f}).seg {GP}.facts off (by omega) hmb hx (by wok_in) (by wok_out)
have hd := afterP_{pv} off c input S _ hb cut1 I1 (by
  rw [← envOf_gdVar _ 2 (by decide), {GP}.facts_rdx _ (rho_ok off) (rho_within off hmb) _ hx (I0.fr {f}).ok,
    envOf_gdVar _ 2 (by decide), {f}.vals (2, {vals[2].lean if cv == 'sym' else f'((({cv} : Nat)) : Int)'}) (by simp [setVal])])
rw [len_{pv}] at hd
intro n hn
exact (Done.run rfl (Done.run rfl hd)) n (by unfold steps at hn; omega)""".split('\n'):
            oo(t)
        return out
    if Mp == 0:
        L.extend(entry_case(2, 'sym'))
    else:
        cases = ' ∨ '.join([f'c = {cv}' for cv in range(Mp)] + [f'{Mp} ≤ c'])
        L.append(f"  have hcs : {cases} := by omega")
        L.append(f"  rcases hcs with {' | '.join(['rfl'] * Mp + ['hM'])}")
        for cv in list(range(Mp)) + ['sym']:
            L.append("  · -- " + (f"c = {cv}" if cv != 'sym' else f"{Mp} ≤ c"))
            L.extend(entry_case(4, cv))
    L.append('')
    prefix_m = 0
    pc_ = entry
    while True:
        prefix_m += 1
        if X.parse(prog[pc_])[0] in ('test', 'cmpi', 'cmpr'):
            break
        pc_ += 1
    open(os.path.join(kdir, 'Lib.lean'), 'w').write(f"""import Keccaktree.Kernels.{d}.All
import Keccaktree.Asm.LibX86
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
/-! GENERATED by lean/x86_glue.py; do not edit.
# `{SYM(kernel)}` as a kernel of the library (any flags/masks at a call or tail call) -/
namespace Keccaktree.Kernels.{d}.Lib
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86
open Keccaktree.Kernels.{d} (prog rodata)

def kernel : Library.KernelThm X86.isa EntryX86 Digest :=
  mkKernel "{SYM(kernel)}" {rank} All.targets rodata prog {entry} All.steps {prefix_m} (by decide +kernel) (by decide +kernel)
    (fun _ _ => by unfold All.steps; omega) All.norm_thm

end Keccaktree.Kernels.{d}.Lib
""")
    open(os.path.join(kdir, 'All.lean'), 'w').write('\n'.join(L) + f'\nend Keccaktree.Kernels.{d}.All\n')
    print('written (exits, body)')


if __name__ == '__main__':
    main()
