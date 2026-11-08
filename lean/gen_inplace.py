#!/usr/bin/env python3
"""In-place hook: footprint summaries of a kernel's generated segments (x86, AArch64, RISC-V).

    gen_inplace.py <Kernel> <Seg>... [--eval] [--split] [--out <dir>]

For each segment directory `Keccaktree/Kernels/<Kernel>/<Seg>` (a generated `Seg.lean` with slice
certificates `cert0 .. certN`), emits `Keccaktree/Kernels/<Kernel>/InPlace/<Seg>.lean` with

    def certs   : the certificate list            theorem chain : ChainOk certs
    theorem len : sum of slice lengths = segLen   theorem sums  : the slices' footprint summaries

(`sums` by `decide +kernel`; its right-hand side is computed first by `#eval`, `--eval` runs it with
`lake env lean`).  The instruction set is read off the certificates' type in `Seg.lean`:

    SliceCert X86.isa X86.isaReloc ...                  -> X86.chain_access   (AliasTrace.lean)
    SliceCert Arm.isa Arm.isaReloc ...                  -> Arm.alIsa.chain_access   (ArmAliasTrace.lean)
    SliceCert (Riscv.isa N) (Riscv.isaReloc N) ...      -> (Riscv.alIsa N).chain_access (RiscvAliasTrace.lean)

`--split`: each slice's summary in its own module `InPlace/<Seg>/S<k>.lean` (theorem `sum`), so that one
lean process holds one slice (the rv64_x1 body summaries in one module peaked at ~19 GB).  lake has no
job limit: build the `S<k>` modules one at a time (e.g. `for k in ...; do lake build ...S$k; done`)
before the segment's module.

The kernel's in-place file then applies `chain_access` with these facts, and the access condition of a
segment at relocation `ρ` reduces to linear inequalities in `ρ.wshift` (`SummOk`).
The generated proof files of the kernel are only read, never modified."""
import os
import re
import subprocess
import sys

args = sys.argv[1:]
run_eval = '--eval' in args
split = '--split' in args
outdir = None
if '--out' in args:
    i = args.index('--out')
    outdir = args[i + 1]
    del args[i:i + 2]
args = [a for a in args if not a.startswith('--')]
K, segs = args[0], args[1:]
root = os.path.dirname(os.path.abspath(__file__))
base = os.path.join(root, 'Keccaktree', 'Kernels', K)
out = outdir or os.path.join(base, 'InPlace')
os.makedirs(out, exist_ok=True)

info = {}
isa_kind = None
for sg in segs:
    seg = open(os.path.join(base, sg, 'Seg.lean')).read()
    n = len(re.findall(r'^def cert\d+ ', seg, re.M))
    m = re.search(r'^def cert0 : SliceCert (.+) rodata prog B where', seg, re.M)
    if not m:
        sys.exit('no certificate type in %s/Seg.lean' % sg)
    ty = m.group(1).strip()
    if ty.startswith('X86.isa '):
        kind = ('x86', None)
    elif ty.startswith('Arm.isa '):
        kind = ('arm', None)
    else:
        mr = re.match(r'\(Riscv\.isa (\S+)\) \(Riscv\.isaReloc \S+\)', ty)
        if not mr:
            sys.exit('unknown instruction set: ' + ty)
        kind = ('rv', mr.group(1))
    if isa_kind is not None and isa_kind != kind:
        sys.exit('segments of different instruction sets')
    isa_kind = kind
    info[sg] = (n, ty)

if isa_kind[0] == 'x86':
    imp, opens = 'Keccaktree.Asm.AliasTrace', 'Keccaktree.Asm Keccaktree.Asm.X86'
    trace, chain_ok = 'traceCells', 'ChainOk'
elif isa_kind[0] == 'arm':
    imp, opens = 'Keccaktree.Asm.ArmAliasTrace', 'Keccaktree.Asm Keccaktree.Asm.X86'
    trace, chain_ok = 'Arm.alIsa.traceCells', 'Arm.alIsa.ChainOk'
else:
    imp, opens = 'Keccaktree.Asm.RiscvAliasTrace', 'Keccaktree.Asm Keccaktree.Asm.X86'
    al = '(Riscv.alIsa %s)' % isa_kind[1]
    trace, chain_ok = al + '.traceCells', al + '.ChainOk'

ev = ['import ' + imp] + ['import Keccaktree.Kernels.%s.%s.Seg' % (K, sg) for sg in segs]
ev += ['open %s Keccaktree.Kernels.%s' % (opens, K)]
for sg in segs:
    lst = ', '.join('%s.cert%d' % (sg, k) for k in range(info[sg][0]))
    ev.append('#eval IO.println ((repr ([%s].map fun C => summ (%s rodata prog C.idx C.cut))).pretty 100000000)'
              % (lst, trace))
evf = os.path.join(out, 'SumEval.lean')
open(evf, 'w').write('\n'.join(ev) + '\n')
def split_summs(v):
    """Split the printed list `[{ ... }, { ... }]` into its elements."""
    v = v.strip()
    if not v.startswith('['):
        return []
    v = v[1:-1]
    out, depth, cur = [], 0, ''
    for ch in v:
        if ch == '{':
            depth += 1
        if ch == '}':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur.strip()); cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


vals = {}
if run_eval:
    r = subprocess.run(['lake', 'env', 'lean', evf], capture_output=True, text=True, cwd=root)
    outs = [l for l in r.stdout.splitlines() if l.startswith('[')]
    if len(outs) != len(segs):
        sys.exit('eval failed:\n' + r.stdout + r.stderr)
    for sg, o in zip(segs, outs):
        # `repr` of Summ: { loR := some 0, hiW := none, ... }; Lean syntax is the same
        vals[sg] = o
for sg in segs:
    n, ty = info[sg]
    lst = ', '.join('%s.cert%d' % (sg, k) for k in range(n))
    chain = 'trivial'
    for _ in range(n - 1):
        chain = '⟨rfl, rfl, %s⟩' % chain
    # one kernel-checked summary per slice (peak memory of one slice), assembled by rewriting
    sv = split_summs(vals.get(sg, ''))
    per_slice = ''
    extra_imports = ''
    for k in range(n):
        rhs = sv[k] if len(sv) == n else 'SUM_%s_%d' % (sg, k)
        stmt = ('summ (%s rodata prog %s.cert%d.idx %s.cert%d.cut) =\n    %s' % (trace, sg, k, sg, k, rhs))
        if split:
            d = os.path.join(out, sg)
            os.makedirs(d, exist_ok=True)
            open(os.path.join(d, 'S%d.lean' % k), 'w').write(
                'import %s\nimport Keccaktree.Kernels.%s.%s.Seg\n'
                '/-! GENERATED by lean/gen_inplace.py: footprint summary of slice %d of `%s`. -/\n'
                'namespace Keccaktree.Kernels.%s.InPlace.%s.S%d\nopen %s Keccaktree.Kernels.%s\n'
                'open Keccaktree.Kernels.%s (prog rodata)\n\nset_option maxRecDepth 100000 in\n'
                'theorem sum : %s := by decide +kernel\n\nend Keccaktree.Kernels.%s.InPlace.%s.S%d\n'
                % (imp, K, sg, k, sg, K, sg, k, opens, K, K, stmt, K, sg, k))
            extra_imports += 'import Keccaktree.Kernels.%s.InPlace.%s.S%d\n' % (K, sg, k)
            per_slice += 'theorem sum%d : %s := S%d.sum\n\n' % (k, stmt, k)
        else:
            per_slice += ('set_option maxRecDepth 100000 in\n'
                          'theorem sum%d : %s := by decide +kernel\n\n' % (k, stmt))
    sum_names = ''.join(', sum%d' % k for k in range(n))
    src = f'''import {imp}
import Keccaktree.Kernels.{K}.{sg}.Seg
{extra_imports}
/-! GENERATED by lean/gen_inplace.py: footprint summaries of segment `{sg}` (in-place hook). -/
namespace Keccaktree.Kernels.{K}.InPlace.{sg}
open {opens} Keccaktree.Kernels.{K}
open Keccaktree.Kernels.{K} (prog rodata)

def certs : List (SliceCert {ty} rodata prog {sg}.B) := [{lst}]

theorem chain : {chain_ok} certs := {chain}

theorem len : (certs.map fun C => C.idx.length).sum = {sg}.segLen := by decide +kernel

{per_slice}
set_option maxRecDepth 100000 in
theorem sums : certs.map (fun C => summ ({trace} rodata prog C.idx C.cut)) =
    {vals.get(sg, 'SUMS_' + sg)} := by
  simp only [certs, List.map_cons, List.map_nil{sum_names}]

end Keccaktree.Kernels.{K}.InPlace.{sg}
'''
    open(os.path.join(out, sg + '.lean'), 'w').write(src)
print('segments:', {s: info[s][0] for s in segs}, isa_kind[0],
      'evaluated' if run_eval else '(run with --eval to fill the sums)')
