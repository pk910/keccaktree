#!/usr/bin/env python3
"""Cross-check that lean/Keccaktree/Generic.lean is a literal transcription of
src/keccak256_generic.c and keccak256_1_generic.go.

Both sources are unrolled, lane-complemented keccak-f implementations
(literal rho offsets and pi destinations, chi row by row). The Lean model
transcribes every round statement by statement. This script parses each round
in every source into SSA form (each assignment gets a fresh version, each use
resolves to the latest version) with the operators as trees, and requires the
statement lists to be equal:

  C   KECCAK_ROUND (all 24 rounds)       = Generic.roundC
  Go  round 0 (sparse initial state)     = Generic.round0Go
  Go  loop body, first half  (E -> A)    = Generic.roundGoEA
  Go  loop body, second half (A -> E)    = Generic.roundGoAE
  Go  round 23 (squeezed row only)       = Generic.round23Go

It also checks the RC tables (C, Go, Lean), the round constants written as
literals (C rounds 0 and 23), and the loop shapes that pick RC[r] / RC[r + 1].
"""
import re, sys, pathlib

repo = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else '.')
c_src = (repo / 'src/keccak256_generic.c').read_text()
go_src = (repo / 'keccak256_1_generic.go').read_text()
lean_src = (repo / 'lean/Keccaktree/Generic.lean').read_text()

ok = True
def report(what, same):
    global ok
    ok &= same
    print('%-44s %s' % (what, 'same' if same else 'DIFFER'))

# ---------------------------------------------------------------- tables

def hexes(body):
    return [int(x, 16) for x in re.findall(r'0x([0-9a-fA-F]+)', body)]

def c_table(src, pat):
    m = re.search(pat, src, re.S)
    assert m, pat
    body = src[m.end():]
    return hexes(body[:body.index('}')])

rc_c = c_table(c_src, r'RC\[24\] = \{')
rc_go = c_table(go_src, r'keccakRC = \[24\]uint64\{')
m = re.search(r'def RC \(\w+ : Nat\) : \w+ :=\s*match \w+ with(.*?)\| _', lean_src, re.S)
assert m, 'Lean RC'
pairs = {int(i): int(v, 16) for i, v in re.findall(r'\|\s*(\d+)\s*=>\s*0x([0-9a-fA-F]+)#64', m.group(1))}
rc_lean = [pairs[i] for i in range(24)]
assert len(rc_c) == len(rc_go) == len(rc_lean) == 24
report('RC table: C vs Lean', rc_c == rc_lean)
report('RC table: Go vs Lean', rc_go == rc_lean)

# ---------------------------------------------------------------- expressions

TOK = re.compile(r'\s*(0x[0-9a-fA-F]+(?:#64|ULL)?|\d+|~~~|\^\^\^|\|\|\||&&&|[A-Za-z_][\w.]*(?:\[[^\]]*\])?|[()^|&~,])')

def tokenize(s):
    s = s.strip()
    out, i = [], 0
    while i < len(s):
        m = TOK.match(s, i)
        assert m and m.end() > i, 'cannot tokenize %r at %r' % (s, s[i:])
        out.append(m.group(1))
        i = m.end()
    return out

BIN = {'^': 'xor', '^^^': 'xor', '|': 'or', '|||': 'or', '&': 'and', '&&&': 'and'}

class P:
    """Expression parser for both syntaxes. A chain of binary operators must use
    one operator (the sources parenthesize every mix), so no precedence rules
    (which differ between C, Go and Lean) are needed."""
    def __init__(self, toks, lean, name):
        self.t, self.i, self.lean, self.name = toks, 0, lean, name
    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None
    def take(self, want=None):
        tok = self.peek()
        assert tok is not None and (want is None or tok == want), (self.name, want, tok, self.t)
        self.i += 1
        return tok
    def expr(self):
        first = self.unary()
        args, op = [first], None
        while self.peek() in BIN:
            o = BIN[self.take()]
            assert op in (None, o), 'unparenthesized operator mix in %s: %s' % (self.name, ' '.join(self.t))
            op = o
            args.append(self.unary())
        return (op, *args) if op else first
    def unary(self):
        tok = self.peek()
        if tok in ('~', '~~~') or (tok == '^' and not self.lean):   # Go's unary ^ is NOT
            self.take()
            return ('not', self.unary())
        return self.atom()
    def atom(self):
        tok = self.take()
        if tok == '(':
            e = self.expr()
            self.take(')')
            return e
        if tok in ('ROL', 'bits.RotateLeft64'):
            if self.lean:                       # ROL x n
                x = self.atom()
                n = self.atom()
            else:                               # ROL(x, n)
                self.take('(')
                x = self.expr()
                self.take(',')
                n = self.expr()
                self.take(')')
            assert n[0] == 'num', (self.name, n)
            return ('rol', x, n[1])
        mh = re.fullmatch(r'0x([0-9a-fA-F]+)(?:#64|ULL)?', tok)
        if mh:
            return ('num', int(mh.group(1), 16))
        if tok.isdigit():
            return ('num', int(tok))
        return ('var', tok)

def ssa(stmts, lean, name, resolve_var):
    """stmts: [(lhs, rhs-text)] in order. Returns [(target, tree)] with versioned names."""
    ver, out, lean_names = {}, [], {}
    def fix(tree):
        if tree[0] == 'var':
            v = tree[1]
            if lean and v in lean_names:
                return ('var', lean_names[v])
            base = resolve_var(v, False)
            if base[0] == 'in':
                return ('in', base[1])
            assert base not in (None,) and base[0] != 'out', '%s: use of %s' % (name, v)
            assert base in ver, '%s: use of %s before definition' % (name, v)
            return ('var', '%s.%d' % (base, ver[base]))
        if tree[0] in ('num',):
            return tree
        if tree[0] == 'rol':
            return ('rol', fix(tree[1]), tree[2])
        return (tree[0], *[fix(a) for a in tree[1:]])
    for lhs, rhs in stmts:
        tree = fix(P(tokenize(rhs), lean, name).expr())
        base = resolve_var(lhs, True)
        assert base is not None, '%s: target %s' % (name, lhs)
        if base[0] == 'out':
            tgt = 'out%d' % base[1]
        else:
            ver[base] = ver.get(base, 0) + 1
            tgt = '%s.%d' % (base, ver[base])
            if lean:
                lean_names[lhs] = tgt
        out.append((tgt, tree))
    return out

# name resolution -------------------------------------------------------

TEMP = re.compile(r'([BCDN])(\d)$')

def c_resolver(inp, outp, rc_name):
    def res(v, is_lhs):
        if v == rc_name:
            return ('in', 'rc')
        m = re.fullmatch(r'%s(\d+)' % inp, v)
        if m:
            assert not is_lhs, 'write to input lane ' + v
            return ('in', int(m.group(1)))
        m = re.fullmatch(r'%s(\d+)' % outp, v)
        if m:
            return ('out', int(m.group(1)))
        m = TEMP.fullmatch(v)
        if m:
            return m.group(1).lower() + m.group(2)
        return None
    return res

LTEMP = re.compile(r'[a-z]([bcdn])(\d)_\d+$')

def lean_resolver(inp, rc_name):
    def res(v, is_lhs):
        if v == rc_name:
            return ('in', 'rc')
        m = re.fullmatch(r'%s\[(\d+)\]' % inp, v)
        if m:
            assert not is_lhs
            return ('in', int(m.group(1)))
        m = re.fullmatch(r'e(\d+)', v)
        if m and is_lhs:
            return ('out', int(m.group(1)))
        m = LTEMP.fullmatch(v)
        if m and is_lhs:
            return m.group(1) + m.group(2)
        return None
    return res

# statement extraction --------------------------------------------------

ASSIGN = re.compile(r'^\s*([A-Za-z_#]\w*(?:##\d+)?)\s*=\s*(.*?);?\s*$')

def c_like_stmts(lines):
    out = []
    for ln in lines:
        ln = ln.split('//')[0].rstrip().rstrip('\\').rstrip()
        ln = re.sub(r'/\*.*?\*/', '', ln)
        ln = ln.replace('##', '')
        ln = ln.strip()
        if not ln or ln.startswith(('do', '}', '#define')):
            continue
        m = ASSIGN.match(ln)
        assert m, 'not an assignment: %r' % ln
        out.append((m.group(1), m.group(2).rstrip(';').strip()))
    return out

def lean_def(name):
    m = re.search(r'^def %s \((\w+) : [^)]*\) \((\w+) : W\) :[^\n]*:=\n(.*?)\n  #v\[([^\]]*)\]' % name, lean_src, re.S | re.M)
    if not m:
        m = re.search(r'^def %s \((\w+) : [^)]*\) :[^\n]*:=\n(.*?)\n  #v\[([^\]]*)\]' % name, lean_src, re.S | re.M)
        assert m, 'Lean def ' + name
        inp, rcn, body, vec = m.group(1), None, m.group(2), m.group(3)
    else:
        inp, rcn, body, vec = m.group(1), m.group(2), m.group(3), m.group(4)
    stmts = []
    for ln in body.split('\n'):
        lm = re.fullmatch(r'\s*let (\w+) := (.*)', ln)
        assert lm, '%s: %r' % (name, ln)
        stmts.append((lm.group(1), lm.group(2)))
    outs = [x.strip() for x in vec.split(',')]
    return inp, rcn, stmts, outs

def compare(label, src_stmts, src_res, lean_name, n_out, rc_tok):
    inp, rcn, lstmts, outs = lean_def(lean_name)
    a = ssa(src_stmts, False, label, src_res)
    b = ssa(lstmts, True, lean_name, lean_resolver(inp, rcn))
    same = a == b and outs == ['e%d' % i for i in range(n_out)]
    written = sorted(int(t[3:]) for t, _ in a if t.startswith('out'))
    same &= written == list(range(n_out))
    if not same:
        for k, (x, y) in enumerate(zip(a, b)):
            if x != y:
                print('  first difference at statement %d:\n    source %s\n    Lean   %s' % (k, x, y))
                break
        else:
            print('  statement counts: source %d, Lean %d' % (len(a), len(b)))
    report('%s = %s' % (label, lean_name), same)

# C: the round macro ------------------------------------------------------
m = re.search(r'#define KECCAK_ROUND\(A, E, rc\)(.*?)\} while \(0\)', c_src, re.S)
assert m, 'KECCAK_ROUND'
c_round = c_like_stmts(m.group(1).split('\n'))
compare('C KECCAK_ROUND', c_round, c_resolver('A', 'E', 'rc'), 'roundC', 25, 'rc')

# C: the node uses RC[0] and RC[23] as literals and RC[r], RC[r + 1] in the loop
calls = re.findall(r'KECCAK_ROUND\((\w), (\w), ([^)]*)\);', c_src)
want = [('A', 'E', '0x%016xULL' % rc_c[0]), ('E', 'A', 'RC[r]'), ('A', 'E', 'RC[r + 1]'),
        ('E', 'A', '0x%016xULL' % rc_c[23])]
report('C round sequence (RC 0, loop RC r / r+1, RC 23)',
       [(x, y, z.lower()) for x, y, z in calls] == [(x, y, z.lower()) for x, y, z in want]
       and 'for (int r = 1; r < 23; r += 2) {' in c_src)
report('Lean nodeC / loopC round sequence',
       'let e := roundC a (RC 0)\n  let e := loopC 1 e 11\n  let a := roundC e (RC 23)' in lean_src
       and '| k + 1 => loopC (r + 2) (roundC (roundC e (RC r)) (RC (r + 1))) k' in lean_src)

# Go: the four sections -----------------------------------------------------
go_lines = go_src.split('\n')
def go_section(start_pat, stop_pat):
    i = next(k for k, l in enumerate(go_lines) if re.search(start_pat, l))
    j = next(k for k in range(i + 1, len(go_lines)) if re.search(stop_pat, go_lines[k]))
    return [l for l in go_lines[i + 1:j] if l.strip() and not l.strip().startswith('//')]

r0 = c_like_stmts(go_section(r'// round 0 ', r'// rounds 1\.\.22'))
loop = c_like_stmts(go_section(r'for rc := 1; rc < 23; rc \+= 2 \{', r'^\t\t\}$'))
r23 = c_like_stmts(go_section(r'// round 23', r'^\s*d := &digests'))
half = len(loop) // 2
assert loop[half][0] == 'C0' and len(loop) == 2 * half, 'Go loop body halves'

compare('Go round 0', r0, c_resolver('A', 'E', None), 'round0Go', 25, None)
compare('Go loop first half (E->A)', loop[:half], c_resolver('E', 'A', 'keccakRC[rc]'), 'roundGoEA', 25, 'rc')
compare('Go loop second half (A->E)', loop[half:], c_resolver('A', 'E', 'keccakRC[rc+1]'), 'roundGoAE', 25, 'rc')
compare('Go round 23', r23, c_resolver('E', 'A', None), 'round23Go', 5, None)
report('Go round 0 / 23 constants = RC[0] / RC[23]',
       ('0x%016x' % rc_go[0]) in ''.join(r for _, r in r0) and ('0x%016x' % rc_go[23]) in ''.join(r for _, r in r23))
report('Lean nodeGo / loopGo round sequence',
       'let e := round0Go (absorbGo l r)\n  let e := loopGo 1 e 11\n  let a := round23Go e' in lean_src
       and '| k + 1 => loopGo (rc + 2) (roundGoAE (roundGoEA e (RC rc)) (RC (rc + 1))) k' in lean_src
       and 'for rc := 1; rc < 23; rc += 2 {' in go_src)

print('ALL ROUNDS AND TABLES MATCH' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
