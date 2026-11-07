#!/usr/bin/env python3
"""Generate the segment proofs of the AArch64 all-count theorems (Keccaktree/Kernels/<Ns>/All.lean).

    gen_segments_arm.py <kernel> [build P]

A kernel's run is cut into segments (`GenS*` modules, `gen_plan_proof.py` in segment mode), each proved once
at every relocated position; the count-dependent instructions between them (`cbz`/`cmp`/`subs`/`sub` of the
count, `csel` on its flags, `b.cond`, `ret`, the tail call) are the concrete lemmas of `Asm/ArmSteps.lean`.
Segments marked `flags` neither read nor write the flags (`seg_flags`: they run from any flags).

Each segment: (gen dir, plan count, entry, end, body?, end-control spec, write-ok, moves, data?, flags?)
  plan count : the recorded run the segment is taken from (`find_plan.py <kernel> <count> <lanes>`)
  body       : the segment hashes (cuts from the plan inside [entry, end), every node advancing)
  end ctl    : list of literal ids and names of other segments ('@GenSX' = that segment's start control words)
"""
import ast, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUTW = lambda n: f'fun p => (p.1 == 3) || (p.1 == 2 && decide (0 ≤ p.2) && decide (p.2 < {4 * n}))'
STACK = 'fun p => p.1 == 3'
NONE = 'fun _ => false'

# kernel: (Ns, lanes, forbid, [segments in generation order])
KERNELS = {
    'scalar_x1': ('ScalarX1', 0, '258,2097411', [
        ('GenSX', 1, 2444, 2450, False, [], NONE, '', False, True),
        ('GenSB', 1, 7, 2442, True, ['@GenSX', 256, 257, 287], OUTW(1), '258:258', True, True),
        ('GenSE1', 1, 0, 6, False, ['@GenSB', '@GenSX'], STACK, '258:258', False, True),
    ]),
}
for k, ns, cbz, subs, ret in (('sha3_x2', 'Sha3X2', 4, 1597, 1603), ('neon_x2', 'NeonX2', 4, 3786, 3792)):
    KERNELS[k] = (ns, 2, '258', [
        ('GenSX', 2, subs + 2, ret, False, [], NONE, '', False, True),
        ('GenSBo', 1, 11, subs, True, ['@GenSX'], OUTW(1), '258:258', True, True),
        ('GenSBe', 2, 11, subs, True, ['@GenSX', 256, 257, 287], OUTW(2), '258:258', True, True),
        ('GenSHa', 3, 9, 11, False, ['@GenSBe'], NONE, '258:258', False, False),
        ('GenSHb', 2, 9, 11, False, ['@GenSBe'], NONE, '258:258', False, False),
        ('GenSHc', 1, 9, 11, False, ['@GenSBo'], NONE, '258:258', False, False),
        ('GenSH', 2, 5, 8, False, ['@GenSHa', '@GenSHb', '@GenSHc'], NONE, '258:258', False, True),
        ('GenSE1', 2, 0, 4, False, ['@GenSH', '@GenSX'], STACK, '258:258', False, True),
    ])

for k, ns, cell, sub, ret in (('sha3_x3', 'Sha3X3', 2097411, 4538, 4553), ('neon_x3', 'NeonX3', 2097379, 6222, 6237)):
    KERNELS[k] = (ns, 2, f'258,{cell}', [
        ('GenSX', 3, sub + 3, ret - 2, False, [256, 257, 287], NONE, '258:258', False, True),
        ('GenSB', 3, 12, sub, True, ['@GenSX', 256, 257, 287], OUTW(3), '258:258', True, True),
        ('GenSE1', 3, 2, 12, False, ['@GenSB'], STACK, '258:258', False, True),
    ])


def ctl0_of(log):
    l = [l for l in open(log).read().splitlines() if l.startswith('control words')][0]
    return ast.literal_eval(l.split(':', 1)[1].strip())[0]


def main():
    kernel = sys.argv[1]
    ns, lanes, forbid, segs = KERNELS[kernel]
    os.chdir(HERE)
    os.makedirs('plans', exist_ok=True)
    plans = {}
    ctl0 = {}
    for (g, count, a, b, body, endc, wok, moves, data, flags) in segs:
        if count not in plans:
            out = subprocess.run(['python3', 'find_plan.py', kernel, str(count), str(lanes)], capture_output=True, text=True, check=True).stdout
            plans[count] = json.loads(out)
        p = plans[count]
        if body:
            cuts = [t for t in p['cuts'] if a < t + 1 < b]
            rounds = [[0] * count] + [[min(i + 1, 24)] * count for i in range(len(cuts))] + [[24] * count]
        else:
            cuts, rounds = [], [[0] * count, [0] * count]
        pf = f'plans/{kernel}_{g}.json'
        json.dump({'kernel': kernel, 'count': count, 'lanes': lanes, 'entry': a, 'end': b, 'cuts': cuts, 'rounds': rounds}, open(pf, 'w'))
        end = set()
        for x in endc:
            end |= set(ctl0[x[1:]]) if isinstance(x, str) else {x}
        env = dict(os.environ, PLAN=pf, OUTDIR=f'Keccaktree/Kernels/{ns}/{g}', GEN=g, NS=f'{ns}.{g}', PROG_NS=ns, ISA='Arm',
                   BATCH='1', SEG='1', END_CTL=','.join(map(str, sorted(end))), FORBID_CTL=forbid, WRITE_OK=wok, MOVES=moves,
                   MOVE_CHAIN='1', DATA='' if data else '0', LOOP='')
        if flags:
            env['FLAG_OBL'] = 'Arm.flagObl'
        subprocess.run(['rm', '-rf', env['OUTDIR']], check=True)
        log = f'plans/gen_{kernel}_{g}.log'
        with open(log, 'w') as f:
            subprocess.run(['python3', 'gen_plan_proof.py', kernel, ns, str(count), str(lanes)], env=env, stdout=f, stderr=subprocess.STDOUT, check=True)
        ctl0[g] = ctl0_of(log)
        print(f'{g}: [{a},{b}) count {count} ctl0 {ctl0[g]} end {sorted(end)}', flush=True)
    # every hand-over target's start control words must be among the end control words the segment before provides
    if len(sys.argv) > 2 and sys.argv[2] == 'build':
        P = sys.argv[3] if len(sys.argv) > 3 else '4'
        for (g, *_r) in reversed(segs):
            k = len([f for f in os.listdir(f'Keccaktree/Kernels/{ns}/{g}') if f.startswith('Slice')])
            subprocess.run(['./build_plan.sh', ns, g, str(k), P])
            r = subprocess.run(['lake', 'build', f'Keccaktree.Kernels.{ns}.{g}.Seg'], capture_output=True, text=True)
            print('\n'.join(l for l in r.stdout.splitlines() if 'error' in l or f'Built Keccaktree.Kernels.{ns}.{g}.Seg' in l), flush=True)


if __name__ == '__main__':
    main()
