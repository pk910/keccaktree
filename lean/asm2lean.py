#!/usr/bin/env python3
"""Translate a kernel object's disassembly into a Lean instruction list.

    asm2lean.py x86 <kernel.o> <FunctionName> <Namespace> > Program.lean

The instruction stream is read from `objdump -d -r` of the object the real
toolchain produced (so the macros of src/*.S are expanded by the assembler,
not reimplemented here); rip-relative constant references are resolved
through the relocation records to offsets in .rodata, whose contents are
emitted too.  Branch targets become instruction indices.
"""
import re
import subprocess
import sys

GPR = {n: i for i, n in enumerate(['rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi',
                                    'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15'])}
GPR32 = {n: i for i, n in enumerate(['eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi'])}
for i in range(8, 16):
    GPR32['r%dd' % i] = i


def gpr(name):
    if name in GPR:
        return GPR[name]
    if name in GPR32:
        return GPR32[name]
    raise ValueError('gpr ' + name)


def imm(s):
    return int(s, 0)


def simm64(s):
    v = int(s, 0)
    if v >= 1 << 63:
        v -= 1 << 64
    return v


class X86:
    LANES = {'xmm': 2, 'ymm': 4, 'zmm': 8}

    def __init__(self, obj, func):
        self.obj = obj
        self.func = func
        dis = subprocess.run(['objdump', '-d', '-r', '--no-show-raw-insn', '-M', 'intel', obj],
                             capture_output=True, text=True, check=True).stdout
        self.lines = dis.splitlines()
        self.rodata = self.section(obj, '.rodata')
        # `.data` (the tail thresholds, `.quad` defaults; a setter the kernels never call
        # may change them at runtime): modelled as constants after the `.rodata` image
        self.data_base = (len(self.rodata) + 7) // 8 * 8
        self.rodata = self.rodata.ljust(self.data_base, b'\0') + self.section(obj, '.data')
        self.parse()

    @staticmethod
    def section(obj, name):
        out = subprocess.run(['objdump', '-s', '-j', name, obj], capture_output=True, text=True).stdout
        data = bytearray()
        for ln in out.splitlines():
            m = re.match(r'^ ([0-9a-f]+) ((?:[0-9a-f]{2,8} ?)+)', ln)
            if m:
                data += bytes.fromhex(m.group(2).replace(' ', ''))
        return data

    def parse(self):
        # pass 1: collect (addr, text, reloc) per instruction
        raw = []
        symaddr = {}
        for ln in self.lines:
            m = re.match(r'^([0-9a-f]+) <([^>]+)>:$', ln)
            if m:
                symaddr[m.group(2)] = int(m.group(1), 16)
                continue
            m = re.match(r'^\s+([0-9a-f]+):\t(.*)$', ln)
            if m:
                raw.append([int(m.group(1), 16), m.group(2).strip(), None])
                continue
            m = re.match(r'^\s+([0-9a-f]+): (R_X86_64_\w+)\t(.*)$', ln)
            if m and raw:
                raw[-1][2] = (int(m.group(1), 16), m.group(2), m.group(3))
        # instruction end addresses
        for i, r in enumerate(raw):
            r.append(raw[i + 1][0] if i + 1 < len(raw) else None)
        self.addr2idx = {r[0]: i for i, r in enumerate(raw)}
        self.entry = self.addr2idx[symaddr[self.func]]
        self.instrs = []
        self.texts = []
        for addr, text, reloc, end in raw:
            self.texts.append(re.sub(r'\s+#.*$', '', text))
            self.instrs.append(self.translate(addr, text, reloc, end))
        self.check_flags()
        self.check_r32()
        self.check_vzeroupper()

    # flag-setting instructions the model implements, and those it does not (data ALU: flags unchanged)
    FLAG_OK = ('.cmpi', '.cmpr', '.cmpm', '.cmprm', '.test', '.dec', '.decm', '.sub', '.xorz', '.bt')
    FLAG_BAD = ('.alu', '.andn', '.add', '.andi', '.shl', '.addm', '.xorm', '.btc')

    def check_flags(self):
        """every conditional jump must be reached, in straight-line code, from a modelled flag setter"""
        targets = set()
        for ins in self.instrs:
            m = re.match(r'^\.(?:jcc \.\w+|jmp|call) (\d+)$', ins)
            if m:
                targets.add(int(m.group(1)))
        for i, ins in enumerate(self.instrs):
            if not ins.startswith('.jcc'):
                continue
            j = i - 1
            while j >= 0:
                op = self.instrs[j].split()[0]
                if op in self.FLAG_OK:
                    # `sub` sets the model's flags only on a number (a pointer leaves them unchanged,
                    # the CPU does not): as a flag source only on the count register rdx
                    if op == '.sub' and self.instrs[j].split()[1] != '2':
                        raise ValueError('flags of sub on a possible pointer (%d %s) used by jcc %d' % (j, self.instrs[j], i))
                    break
                if op in self.FLAG_BAD or op in ('.jmp', '.jcc', '.call', '.ret', '.tailcall', '.repmovsb') or j in targets:
                    raise ValueError('flags of instruction %d (%s) used by jcc %d are not modelled' % (j, self.instrs[j], i))
                j -= 1
            else:
                raise ValueError('jcc %d without a flag setter' % i)

    def succs(self, i):
        """control-flow successors of instruction i (calls: the callee; returns: every return site)"""
        ins = self.instrs[i]
        op = ins.split()[0]
        m = re.match(r'^\.(?:jcc \.\w+|jmp|call) (\d+)$', ins)
        if op == '.jmp':
            return [int(m.group(1))]
        if op == '.jcc':
            return [int(m.group(1)), i + 1]
        if op == '.call':
            return [int(m.group(1))]
        if op == '.ret':
            return [k + 1 for k, x in enumerate(self.instrs) if x.startswith('.call ')]
        if op in ('.tailcall',):
            return []
        return [i + 1] if i + 1 < len(self.instrs) else []

    # 32-bit general-register forms: the model's 64-bit semantics agree with the CPU's 32-bit
    # operation only when the upper half of the register is zero.  Allowed: zero-extending writes
    # (`mov r32, imm >= 0`, `xor r32, r32`, `dec r32`) anywhere; reads (`dec r32`, `cmp r32, imm >= 0`,
    # `test r32, r32`) only where a forward must-analysis shows the upper half is zero.
    R32_WRITE = re.compile(r'^(mov\s+(e[a-d]x|e[sd]i|e[sb]p|r\d+d),\s*0x[0-9a-f]+|xor\s+(\w+),\s*\3|dec\s+(e[a-d]x|e[sd]i|e[sb]p|r\d+d))$')
    R32_READ = re.compile(r'^(dec\s+(\w+)|cmp\s+(\w+),\s*0x[0-9a-f]+|test\s+(\w+),\s*\4)$')

    def gpr_writes(self, i):
        """64-bit register numbers instruction i writes (by its text)"""
        t = self.texts[i]
        parts = t.split(None, 1)
        op = parts[0]
        args = self.split_args(parts[1]) if len(parts) > 1 else []
        ws = set()
        if op in ('cmp', 'test', 'bt', 'push', 'jmp', 'call', 'ret', 'nop', 'nopw', 'nopl', 'data16', 'cs', 'vzeroupper') \
                or op.startswith('j') or op == 'kmovw':
            pass
        elif op == 'rep':
            ws = {1, 6, 7}
        elif op == 'xchg' and len(args) == 2:
            ws = {gpr(a) for a in args if a in GPR or a in GPR32}
        elif op == 'pop':
            ws = {gpr(args[0]), 4}
        elif args and (args[0] in GPR or args[0] in GPR32):
            ws = {gpr(args[0])}
        if op in ('push', 'call', 'ret'):
            ws.add(4)
        return ws

    def check_r32(self):
        uses = [i for i, t in enumerate(self.texts) if re.search(r'\b(e[a-d]x|e[sd]i|e[sb]p|r\d+d)\b', t)]
        if not uses:
            return
        for i in uses:
            t = self.texts[i]
            if not (self.R32_WRITE.match(t) or self.R32_READ.match(t)):
                raise ValueError('32-bit form not modelled: %d %s' % (i, t))
            m = re.match(r'^mov\s+\w+,\s*0x([0-9a-f]+)$', t)
            if m and int(m.group(1), 16) >= 1 << 31:
                raise ValueError('32-bit immediate (sign-extended by the model): %d %s' % (i, t))
        n = len(self.instrs)
        ALL = frozenset(range(16))
        # must-analysis: Z = registers whose upper half is zero, NZ = registers known non-zero (32-bit)
        top = (ALL, ALL)
        st = [top] * n
        st[self.entry] = (frozenset(), frozenset())
        succ = [self.succs(i) for i in range(n)]

        def out(i, j):
            z, nz = set(st[i][0]), set(st[i][1])
            ws = self.gpr_writes(i)
            z -= ws
            nz -= ws
            t = self.texts[i]
            if self.R32_WRITE.match(t):
                z |= ws
                m = re.match(r'^mov\s+\w+,\s*0x([0-9a-f]+)$', t)
                if m and int(m.group(1), 16) != 0:
                    nz |= ws
            # a taken `jne` after `dec r32` / `test r32, r32`: the register is non-zero
            if t.split()[0] in ('jne', 'jnz') and i > 0 and j != i + 1:
                p = self.texts[i - 1]
                m = re.match(r'^(?:dec\s+(\w+)|test\s+(\w+),\s*\2)$', p)
                if m and (m.group(1) or m.group(2)) in GPR32:
                    nz.add(gpr(m.group(1) or m.group(2)))
            return frozenset(z), frozenset(nz)
        changed = True
        while changed:
            changed = False
            ins = [[] for _ in range(n)]
            for i in range(n):
                for j in succ[i]:
                    if j < n:
                        ins[j].append(out(i, j))
            for i in range(n):
                if i == self.entry:
                    continue
                ps = ins[i]
                v = (frozenset.intersection(*[p[0] for p in ps]), frozenset.intersection(*[p[1] for p in ps])) if ps else top
                if v != st[i]:
                    st[i] = v
                    changed = True
        for i in uses:
            m = self.R32_READ.match(self.texts[i])
            if not m:
                continue
            r = gpr(m.group(2) or m.group(3) or m.group(4))
            if r not in st[i][0]:
                raise ValueError('32-bit read of a register whose upper half may be non-zero: %d %s' % (i, self.texts[i]))
            if m.group(2) and r not in st[i][1]:
                raise ValueError('32-bit dec of a register that may be zero (wraps to 2^32-1 on the CPU): %d %s' % (i, self.texts[i]))

    def check_vzeroupper(self):
        """the model's `vzeroupper` keeps the upper lanes: no vector instruction may follow it before the
        function returns or tail-calls (the CPU zeroes bits 128.. of ymm/zmm0-15)"""
        for i, ins in enumerate(self.instrs):
            if ins != '.vzeroupper':
                continue
            seen, todo = set(), [i + 1]
            while todo:
                j = todo.pop()
                if j in seen or j >= len(self.instrs):
                    continue
                seen.add(j)
                op = self.instrs[j].split()[0]
                if op.startswith('.v') and op != '.vzeroupper' or op in ('.kmovw',):
                    raise ValueError('vector instruction %d (%s) after vzeroupper %d' % (j, self.instrs[j], i))
                if op == '.ret':
                    continue
                if op == '.call':
                    raise ValueError('call after vzeroupper %d' % i)
                todo.extend(self.succs(j))

    def rodata_target(self, reloc, end):
        off, typ, val = reloc
        m = re.match(r'^(\.rodata|\.data)([+-]0x[0-9a-f]+)?$', val)
        if not m:
            raise ValueError('reloc ' + val)
        a = int(m.group(2), 16) if m.group(2) else 0
        return a + (end - off) + (self.data_base if m.group(1) == '.data' else 0)

    def memop(self, s, reloc, end):
        s = s.strip()
        m = re.match(r'^(?:[A-Z]+WORD PTR |QWORD BCST |WORD PTR )?\[(\w+)(?:([+-])0x([0-9a-f]+))?\]', s)
        if not m:
            raise ValueError('mem ' + s)
        base, sign, disp = m.group(1), m.group(2), m.group(3)
        d = int(disp, 16) if disp else 0
        if sign == '-':
            d = -d
        if base == 'rip':
            return '(.rip %d)' % self.rodata_target(reloc, end)
        return '(.base %d (%d))' % (gpr(base), d)

    def src(self, s, reloc, end):
        s = s.strip()
        m = re.match(r'^(xmm|ymm|zmm)(\d+)$', s)
        if m:
            return '(.reg %d)' % int(m.group(2))
        if s.startswith('QWORD BCST'):
            return '(.bcst %s)' % self.memop(s, reloc, end)
        return '(.mem %s)' % self.memop(s, reloc, end)

    def vreg(self, s):
        m = re.match(r'^(xmm|ymm|zmm)(\d+)(\{k(\d)\})?$', s.strip())
        if not m:
            raise ValueError('vreg ' + s)
        return self.LANES[m.group(1)], int(m.group(2)), (int(m.group(4)) if m.group(3) else None)

    def target(self, s):
        m = re.match(r'^([0-9a-f]+) <', s.strip())
        return self.addr2idx[int(m.group(1), 16)]

    def translate(self, addr, text, reloc, end):
        text = re.sub(r'\s+#.*$', '', text)
        parts = text.split(None, 1)
        op = parts[0]
        args = [a for a in self.split_args(parts[1])] if len(parts) > 1 else []
        if op == 'xchg' and args[0] != args[1]:
            return '.xchg %d %d' % (gpr(args[0]), gpr(args[1]))
        if op in ('nop', 'data16', 'cs', 'nopw', 'nopl', 'xchg'):
            return '.nop'
        if op in ('vmovdqu', 'vmovdqa', 'vmovdqa64', 'vmovdqu64'):
            if re.match(r'^[xyz]mm', args[0]):
                lanes, d, mask = self.vreg(args[0])
                return '.vmov %d %d %s %s' % (lanes, d, self.src(args[1], reloc, end), 'none' if mask is None else '(some %d)' % mask)
            lanes, s_, _ = self.vreg(args[1])
            return '.vstore %d %s %d' % (lanes, self.memop(args[0], reloc, end), s_)
        two = {'vpxor': 'vpxor', 'vpxorq': 'vpxor', 'vpand': 'vpand', 'vpandq': 'vpand', 'vpandn': 'vpandn',
               'vpandnq': 'vpandn', 'vpor': 'vpor', 'vporq': 'vpor', 'vpaddq': 'vpaddq',
               'vpunpcklqdq': 'vpunpcklqdq', 'vpunpckhqdq': 'vpunpckhqdq', 'vpshufb': 'vpshufb',
               'vpermt2q': 'vpermt2q'}
        if op in two:
            lanes, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.%s %d %d %d %s' % (two[op], lanes, d, a, self.src(args[2], reloc, end))
        if op in ('vpsllq', 'vpsrlq', 'vprolq'):
            lanes, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.%s %d %d %d %d' % (op, lanes, d, a, imm(args[2]))
        if op in ('vpternlogq', 'vshufi64x2'):
            lanes, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.%s %d %d %d %s %d' % (op, lanes, d, a, self.src(args[2], reloc, end), imm(args[3]))
        if op == 'vperm2i128':
            _, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.vperm2i128 %d %d %s %d' % (d, a, self.src(args[2], reloc, end), imm(args[3]))
        if op == 'vinserti128':
            _, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.vinserti128 %d %d %s %d' % (d, a, self.src(args[2], reloc, end), imm(args[3]))
        if op == 'vextracti128':
            _, a, _ = self.vreg(args[1])
            return '.vextracti128 %s %d %d' % (self.memop(args[0], reloc, end), a, imm(args[2]))
        if op in ('vpsllvq', 'vpsrlvq'):
            lanes, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.%s %d %d %d %s' % (op, lanes, d, a, self.src(args[2], reloc, end))
        if op in ('vpblendd', 'vpalignr'):
            lanes, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.%s %d %d %d %s %d' % (op, lanes, d, a, self.src(args[2], reloc, end), imm(args[3]))
        if op == 'vpshufd':
            lanes, d, _ = self.vreg(args[0])
            _, a, _ = self.vreg(args[1])
            return '.vpshufd %d %d %d %d' % (lanes, d, a, imm(args[2]))
        if op == 'kmovw':
            mo = self.memop(args[1], reloc, end)
            # the model reads the 16-bit mask from one 8-byte word: the byte offset must be known and <= 6
            m = re.match(r'^\(\.rip (\d+)\)$', mo)
            if not m or int(m.group(1)) % 8 == 7:
                raise ValueError('kmovw from a base register or across a word boundary: %x %s' % (addr, text))
            return '.kmovw %d %s' % (int(args[0][1:]), mo)
        if op == 'vzeroupper':
            return '.vzeroupper'
        def gsrc(a):
            if a.startswith('QWORD PTR'):
                return '(.mem %s)' % self.memop(a, reloc, end)
            if re.match(r'^-?0x[0-9a-f]+$', a):
                return '(.imm (%d))' % simm64(a)
            return '(.reg %d)' % gpr(a)
        isimm = lambda a: re.match(r'^-?0x[0-9a-f]+$', a) is not None
        ismem = lambda a: a.startswith('QWORD PTR')
        if op in ('mov', 'movabs'):
            if ismem(args[0]):
                if isimm(args[1]):
                    return '.storeqi %s (%d)' % (self.memop(args[0], reloc, end), simm64(args[1]))
                return '.storeq %s %d' % (self.memop(args[0], reloc, end), gpr(args[1]))
            if ismem(args[1]):
                return '.loadq %d %s' % (gpr(args[0]), self.memop(args[1], reloc, end))
            if isimm(args[1]):
                return '.movi %d (%d)' % (gpr(args[0]), simm64(args[1]))
            return '.mov %d %d' % (gpr(args[0]), gpr(args[1]))
        if op == 'lea':
            return '.lea %d %s' % (gpr(args[0]), self.memop(args[1], reloc, end))
        if op == 'add' and ismem(args[0]):
            return '.addm %s (%d)' % (self.memop(args[0], reloc, end), simm64(args[1]))
        if op in ('add', 'sub') and isimm(args[1]):
            if op == 'sub' and simm64(args[1]) < 0:
                raise ValueError('sub with a negative immediate (flags not modelled): %x %s' % (addr, text))
            return '.%s %d (%d)' % (op, gpr(args[0]), simm64(args[1]))
        if op == 'and' and args[0] == 'rsp':
            return '.andi %d (%d)' % (gpr(args[0]), simm64(args[1]))
        if op == 'shl':
            return '.shl %d %d' % (gpr(args[0]), imm(args[1]))
        if op == 'dec':
            if ismem(args[0]):
                return '.decm %s' % self.memop(args[0], reloc, end)
            return '.dec %d' % gpr(args[0])
        if op == 'xor' and args[0] == args[1]:
            return '.xorz %d' % gpr(args[0])
        if op == 'xor' and ismem(args[0]):
            return '.xorm %s %d' % (self.memop(args[0], reloc, end), gpr(args[1]))
        if op in ('xor', 'and', 'or', 'add'):
            return '.alu .%s %d %s' % (op, gpr(args[0]), gsrc(args[1]))
        if op == 'andn':
            return '.andn %d %d %s' % (gpr(args[0]), gpr(args[1]), gsrc(args[2]))
        if op == 'rorx':
            return '.rorx %d %s %d' % (gpr(args[0]), gsrc(args[1]), imm(args[2]))
        if op == 'cmp':
            if ismem(args[0]):
                return '.cmpm %s %d' % (self.memop(args[0], reloc, end), gpr(args[1]))
            if ismem(args[1]):
                return '.cmprm %d %s' % (gpr(args[0]), self.memop(args[1], reloc, end))
            if isimm(args[1]):
                if simm64(args[1]) < 0:
                    raise ValueError('cmp with a negative immediate (the model compares signed offsets): %x %s' % (addr, text))
                return '.cmpi %d (%d)' % (gpr(args[0]), simm64(args[1]))
            return '.cmpr %d %d' % (gpr(args[0]), gpr(args[1]))
        if op == 'test':
            return '.test %d %d' % (gpr(args[0]), gpr(args[1]))
        if op == 'bt':
            return '.bt %d %d' % (gpr(args[0]), gpr(args[1]))
        if op == 'btc':
            return '.btc %d %d' % (gpr(args[0]), imm(args[1]))
        if op in ('je', 'jne', 'jb', 'ja', 'jae', 'jbe', 'jz', 'jnz', 'jc', 'jnc'):
            c = {'je': 'e', 'jz': 'e', 'jne': 'ne', 'jnz': 'ne', 'jb': 'b', 'jc': 'b', 'ja': 'a', 'jae': 'ae', 'jnc': 'ae', 'jbe': 'be'}[op]
            if reloc and 'PLT32' in reloc[1]:
                return '.jcct .%s "%s"' % (c, reloc[2].split('-')[0])
            return '.jcc .%s %d' % (c, self.target(args[0]))
        if op == 'jmp':
            if reloc and 'PLT32' in reloc[1]:
                return '.tailcall "%s"' % reloc[2].split('-')[0]
            return '.jmp %d' % self.target(args[0])
        if op == 'call':
            return '.call %d' % self.target(args[0])
        if op == 'ret':
            return '.ret'
        if op == 'push':
            return '.push %d' % gpr(args[0])
        if op == 'pop':
            return '.pop %d' % gpr(args[0])
        if op == 'rep':
            return '.repmovsb'
        raise ValueError('unhandled: %x %s' % (addr, text))

    @staticmethod
    def split_args(s):
        out, depth, cur = [], 0, ''
        for ch in s:
            if ch == '[':
                depth += 1
            elif ch == ']':
                depth -= 1
            if ch == ',' and depth == 0:
                out.append(cur.strip()); cur = ''
            else:
                cur += ch
        if cur.strip():
            out.append(cur.strip())
        return out

    def emit(self, ns, out):
        out.write('import Keccaktree.Asm.X86\n')
        out.write('/-! GENERATED by lean/asm2lean.py from %s (objdump -d -r); do not edit. -/\n' % self.obj.split('/')[-1])
        out.write('namespace %s\nopen Keccaktree.Asm.X86\n\n' % ns)
        out.write('set_option maxRecDepth 100000 in\n')
        out.write('/-- `%s` and its local batch routine, one entry per instruction. -/\n' % self.func)
        out.write('def prog : Array Instr := #[\n')
        for i, ins in enumerate(self.instrs):
            out.write('  %s%s  -- %d\n' % (ins, ',' if i + 1 < len(self.instrs) else '', i))
        out.write(']\n\n')
        words = [int.from_bytes(self.rodata[i:i + 8].ljust(8, b'\0'), 'little') for i in range(0, len(self.rodata), 8)]
        out.write('/-- `.rodata`, as 64-bit words. -/\ndef rodata : Array (BitVec 64) := #[\n')
        for i in range(0, len(words), 4):
            out.write('  ' + ', '.join('0x%016x#64' % w for w in words[i:i + 4]) + (',' if i + 4 < len(words) else '') + '\n')
        out.write(']\n\n')
        out.write('/-- Instruction index of the function entry. -/\ndef entry : Nat := %d\n\n' % self.entry)
        out.write('end %s\n' % ns)




class Arm:
    """AArch64 (objdump default syntax) → Keccaktree.Asm.Arm.Instr"""
    def __init__(self, obj, func):
        self.obj, self.func = obj, func
        dis = subprocess.run(['aarch64-linux-gnu-objdump', '-d', '-r', '-z', '--no-show-raw-insn', obj],
                             capture_output=True, text=True, check=True).stdout
        raw, symaddr, words = [], {}, {}
        self.reloc = {}
        for ln in dis.splitlines():
            m = re.match(r'^([0-9a-f]+) <([^>]+)>:$', ln)
            if m: symaddr[m.group(2)] = int(m.group(1), 16); continue
            m = re.match(r'^\s+([0-9a-f]+): (R_AARCH64_\w+)\t(\S+)', ln)
            if m: self.reloc[int(m.group(1), 16)] = (m.group(2), m.group(3)); continue
            m = re.match(r'^\s+([0-9a-f]+):\t(.*)$', ln)
            if m:
                addr, text = int(m.group(1), 16), m.group(2).strip()
                raw.append((addr, text))
                mw = re.match(r'^\.word\s+0x([0-9a-f]+)', text)
                if mw: words[addr] = int(mw.group(1), 16)
        self.words = words
        self.addr2idx = {a: i for i, (a, _) in enumerate(raw)}
        self.entry = self.addr2idx[symaddr[self.func]]
        self.instrs = [self.translate(a, t) for a, t in raw]
        self.check_dload()

    def check_dload(self):
        """`ldr d`/`ldp d` leave lane 1 of the register unchanged in the model, the CPU zeroes it: no vector
        instruction and no q/d store may follow before the function returns or tail-calls"""
        for i, ins in enumerate(self.instrs):
            if not re.match(r'^\.(ldr|ldp) \(\.d ', ins):
                continue
            seen, todo = set(), [i + 1]
            while todo:
                j = todo.pop()
                if j in seen or j >= len(self.instrs):
                    continue
                seen.add(j)
                x = self.instrs[j]
                op = x.split()[0]
                if re.match(r'^\.(ldr|ldp) \(\.d ', x) or re.match(r'^\.(ldr|ldp|str|stp) \(\.x ', x) or op in (
                        '.eorx', '.bicx', '.rorx', '.movx', '.movi', '.add', '.sub', '.subs', '.cmp', '.csel', '.nop'):
                    todo.append(j + 1)
                    continue
                if op in ('.ret', '.tailcall'):
                    continue
                m = re.match(r'^\.(cbz \d+|bcond \.\w+|b) (\d+)$', x)
                if m:
                    todo.append(int(m.group(2)))
                    if op != '.b':
                        todo.append(j + 1)
                    continue
                raise ValueError('instruction %d (%s) after the d-register load %d (%s)' % (j, x, i, ins))

    def word64(self, addr):
        return self.words[addr] | (self.words[addr + 4] << 32)

    @staticmethod
    def vreg(s):
        m = re.match(r'^v(\d+)\.(16b|2d)$', s.strip()); return int(m.group(1))

    @staticmethod
    def xreg(s):
        s = s.strip()
        if s == 'sp': return 31
        m = re.match(r'^[xw](\d+)$', s); return int(m.group(1))

    @staticmethod
    def lreg(s):
        s = s.strip()
        if s == 'sp': return '(.x 31)'
        m = re.match(r'^([xwqd])(\d+)$', s)
        return '(.%s %d)' % (m.group(1).replace('w', 'x'), int(m.group(2)))

    @staticmethod
    def imm(s):
        return int(s.strip().lstrip('#'), 0)

    def target(self, s):
        m = re.match(r'^([0-9a-f]+) <', s.strip()); return self.addr2idx[int(m.group(1), 16)]

    def memop(self, s):
        """[base], [base, #off], [base, #off]!, [base], #off  -> (base, off, wb)"""
        s = s.strip()
        m = re.match(r'^\[(\w+)\], #(-?\w+)$', s)
        if m: return self.xreg(m.group(1)), self.imm(m.group(2)), 2
        m = re.match(r'^\[(\w+), #(-?\w+)\](!?)$', s)
        if m: return self.xreg(m.group(1)), self.imm(m.group(2)), (1 if m.group(3) else 0)
        m = re.match(r'^\[(\w+)\]$', s)
        if m: return self.xreg(m.group(1)), 0, 0
        raise ValueError('mem ' + s)

    def translate(self, addr, text):
        text = re.sub(r'\s*//.*$', '', text)
        if text.startswith('.word'): return '.data'
        parts = text.split(None, 1)
        op = parts[0]
        args = [a.strip() for a in re.split(r',(?![^\[]*\])', parts[1])] if len(parts) > 1 else []
        V, X, I = self.vreg, self.xreg, self.imm
        if op in ('nop',): return '.nop'
        if op == 'ret': return '.ret'
        if op == 'eor' and args[0].startswith('v'): return '.eor %d %d %d' % (V(args[0]), V(args[1]), V(args[2]))
        if op == 'bic' and args[0].startswith('v'): return '.bic %d %d %d' % (V(args[0]), V(args[1]), V(args[2]))
        if op == 'eor3': return '.eor3 %d %d %d %d' % tuple(V(a) for a in args)
        if op == 'bcax': return '.bcax %d %d %d %d' % tuple(V(a) for a in args)
        if op == 'rax1': return '.rax1 %d %d %d' % tuple(V(a) for a in args)
        if op == 'xar': return '.xar %d %d %d %d' % (V(args[0]), V(args[1]), V(args[2]), I(args[3]))
        if op == 'shl': return '.shl %d %d %d' % (V(args[0]), V(args[1]), I(args[2]))
        if op == 'sri': return '.sri %d %d %d' % (V(args[0]), V(args[1]), I(args[2]))
        if op in ('zip1', 'zip2'): return '.%s %d %d %d' % (op, V(args[0]), V(args[1]), V(args[2]))
        if op == 'add' and args[0].startswith('v'): return '.addv %d %d %d' % (V(args[0]), V(args[1]), V(args[2]))
        if op == 'tbl':
            m = re.match(r'^v(\d+)\.16b, \{v(\d+)\.16b\}, v(\d+)\.16b$', ', '.join(args))
            return '.tbl %d %d %d' % (int(m.group(1)), int(m.group(2)), int(m.group(3)))
        if op == 'mov' and args[0].startswith('v'): return '.movv %d %d' % (V(args[0]), V(args[1]))
        if op == 'movi': assert I(args[1]) == 0; return '.movi0 %d' % V(args[0])
        if op in ('eor', 'bic'):
            ror = I(args[3].split()[1]) if len(args) == 4 else 0
            return '.%sx %d %d %d %d' % (op, X(args[0]), X(args[1]), X(args[2]), ror)
        if op == 'ror': return '.rorx %d %d %d' % (X(args[0]), X(args[1]), I(args[2]))
        if op == 'mov':
            if args[1].startswith('#'): return '.movi %d (0x%x#64)' % (X(args[0]), I(args[1]) & ((1 << 64) - 1))
            return '.movx %d %d' % (X(args[0]), X(args[1]))
        if op in ('add', 'sub', 'subs'): return '.%s %d %d (%d)' % (op, X(args[0]), X(args[1]), I(args[2]))
        if op == 'cmp': return '.cmp %d (%d)' % (X(args[0]), I(args[1]))
        if op == 'csel': return '.csel %d %d %d .%s' % (X(args[0]), X(args[1]), X(args[2]), args[3])
        if op == 'ldr':
            if args[1].startswith('['):
                # the memory operand is everything after the register (`[x1], #8` is post-indexed)
                b, o, wb = self.memop(', '.join(args[1:])); assert wb == 0, text
                return '.ldr %s %d (%d)' % (self.lreg(args[0]), b, o)
            m = re.match(r'^([0-9a-f]+) <', args[1]); a = int(m.group(1), 16)
            r = self.lreg(args[0])
            if r.startswith('(.q'): return '.ldrlit %s (0x%016x#64) (0x%016x#64)' % (r, self.word64(a), self.word64(a + 8))
            return '.ldrlit %s (0x%016x#64) (0#64)' % (r, self.word64(a))
        if op == 'str':
            b, o, wb = self.memop(', '.join(args[1:])); assert wb == 0, text
            return '.str %s %d (%d)' % (self.lreg(args[0]), b, o)
        if op in ('ldp', 'stp'):
            # `[sp], #16` (post-index) is split into two arguments by the comma split above: rejoin, or
            # the write-back of the base register is lost
            b, o, wb = self.memop(', '.join(args[2:]))
            return '.%s %s %s %d (%d) %d' % (op, self.lreg(args[0]), self.lreg(args[1]), b, o, wb)
        if op == 'cbz': return '.cbz %d %d' % (X(args[0]), self.target(args[1]))
        if op.startswith('b.'):
            c = op[2:]; c = {'hs': 'cs', 'lo': 'cc'}.get(c, c)
            return '.bcond .%s %d' % (c, self.target(args[0]))
        if op == 'b':
            if addr in self.reloc:
                kind, sym = self.reloc[addr]; assert kind == 'R_AARCH64_JUMP26', kind
                return '.tailcall "%s"' % sym
            return '.b %d' % self.target(args[0])
        raise ValueError('unhandled: %x %s' % (addr, text))

    def emit(self, ns, out):
        out.write('import Keccaktree.Asm.Arm\n')
        out.write('/-! GENERATED by lean/asm2lean.py from %s (aarch64 objdump -d); do not edit. -/\n' % self.obj.split('/')[-1])
        out.write('namespace %s\nopen Keccaktree.Asm.Arm\n\n' % ns)
        out.write('set_option maxRecDepth 100000 in\ndef prog : Array Instr := #[\n')
        for i, ins in enumerate(self.instrs):
            out.write('  %s%s  -- %d\n' % (ins, ',' if i + 1 < len(self.instrs) else '', i))
        out.write(']\n\n/-- No separate constants section: literals are inlined. -/\ndef rodata : Array (BitVec 64) := #[]\n\n')
        out.write('def entry : Nat := %d\n\nend %s\n' % (self.entry, ns))


class Riscv:
    """RISC-V (objdump default syntax) → Keccaktree.Asm.Riscv.Instr"""
    REGS = {'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4, 't0': 5, 't1': 6, 't2': 7, 's0': 8, 'fp': 8, 's1': 9,
            'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17,
            's2': 18, 's3': 19, 's4': 20, 's5': 21, 's6': 22, 's7': 23, 's8': 24, 's9': 25, 's10': 26, 's11': 27,
            't3': 28, 't4': 29, 't5': 30, 't6': 31}

    def __init__(self, obj, func):
        self.obj, self.func = obj, func
        dis = subprocess.run(['riscv64-linux-gnu-objdump', '-d', '-r', '--no-show-raw-insn', obj],
                             capture_output=True, text=True, check=True).stdout
        raw, symaddr = [], {}
        self.reloc = {}
        for ln in dis.splitlines():
            m = re.match(r'^([0-9a-f]+) <([^>]+)>:$', ln)
            if m: symaddr[m.group(2)] = int(m.group(1), 16); continue
            m = re.match(r'^\s+([0-9a-f]+): (R_RISCV_\w+)\t(\S+)', ln)
            if m: self.reloc.setdefault(int(m.group(1), 16), []).append((m.group(2), m.group(3))); continue
            m = re.match(r'^\s+([0-9a-f]+):\t(.*)$', ln)
            if m:
                addr, text = int(m.group(1), 16), m.group(2).strip()
                raw.append((addr, text))
        self.addr2idx = {a: i for i, (a, _) in enumerate(raw)}
        self.entry = self.addr2idx[symaddr[self.func]]
        # the constants (.rodata: the 24 round constants)
        sec = subprocess.run(['riscv64-linux-gnu-objdump', '-s', '-j', '.rodata', obj],
                             capture_output=True, text=True, check=True).stdout
        data = b''
        for ln in sec.splitlines():
            m = re.match(r'^ ([0-9a-f]{4}) ((?:[0-9a-f]{8} ?){1,4})', ln)
            if m: data += bytes.fromhex(m.group(2).replace(' ', ''))
        self.rodata = [int.from_bytes(data[i:i + 8], 'little') for i in range(0, len(data) - len(data) % 8, 8)]
        self.instrs = [self.translate(a, t) for a, t in raw]
        # `auipc rd, %pcrel_hi(.LRC+o)` is modelled as `rd := the address of .LRC+o`; the CPU leaves only the
        # pc-relative high part in rd, and the low part is added by the next instruction (`addi rd, rd,
        # %pcrel_lo` -- shown as `mv rd, rd` before relocation -- or `ld rd, %pcrel_lo(rd)`).  Faithful iff
        # that pair is adjacent: the model's `mv`/`ld ..(0)` then sees the full address.
        for i, ins in enumerate(self.instrs):
            if ins.startswith('.lea '):
                rd = ins.split()[1]
                nxt = self.instrs[i + 1] if i + 1 < len(self.instrs) else ''
                lo = [r for r in self.reloc.get(raw[i + 1][0], []) if r[0] in ('R_RISCV_PCREL_LO12_I', 'R_RISCV_PCREL_LO12_S')] \
                    if i + 1 < len(raw) else []
                if not lo or not re.match(r'^\.(ld %s %s \(0\)|mv %s %s)$' % (rd, rd, rd, rd), nxt):
                    raise ValueError('auipc %d not paired with its %%pcrel_lo addi/ld (%s)' % (i, nxt))
        self.check_shift_counts()

    def check_shift_counts(self):
        """`vsll.vx`/`vsrl.vx`/`vror.vx`: the model shifts by the register value if it is < 64 (else 0);
        the CPU by its low 6 bits.  Require (forward must-analysis) that the count register holds a
        `li` constant < 64 on every path."""
        n = len(self.instrs)
        succ = []
        for i, x in enumerate(self.instrs):
            m = re.match(r'^\.(br \.\w+ \d+ \d+|j) (\d+)$', x)
            if x == '.ret':
                succ.append([])
            elif m:
                succ.append([int(m.group(2))] + ([i + 1] if x.startswith('.br') else []))
            else:
                succ.append([i + 1] if i + 1 < n else [])
        TOP = None   # unvisited
        st = [TOP] * n
        st[self.entry] = {}
        def out(i):
            d = dict(st[i])
            x = self.instrs[i]
            m = re.match(r'^\.(op|opi|li|mv|not|lea|ld|vsetvli) (\d+)', x)
            if m:
                d.pop(int(m.group(2)), None)
                ml = re.match(r'^\.li (\d+) \(0x([0-9a-f]+)#64\)$', x)
                if ml and int(ml.group(2), 16) < 64:
                    d[int(ml.group(1))] = int(ml.group(2), 16)
            return d
        changed = True
        while changed:
            changed = False
            for i in range(n):
                if st[i] is TOP:
                    continue
                o = out(i)
                for j in succ[i]:
                    if j >= n:
                        continue
                    new = o if st[j] is TOP else {k: v for k, v in st[j].items() if o.get(k) == v}
                    if st[j] is TOP or new != st[j]:
                        if st[j] is TOP or len(new) < len(st[j]):
                            st[j] = new
                            changed = True
        for i, x in enumerate(self.instrs):
            m = re.match(r'^\.vshiftx \d+ \d+ \.\w+ (\d+)$', x)
            if m and st[i] is not TOP and int(m.group(1)) not in st[i]:
                raise ValueError('vector shift count register x%s at %d is not a constant < 64' % (m.group(1), i))

    def reg(self, s):
        return self.REGS[s.strip()]

    @staticmethod
    def vreg(s):
        m = re.match(r'^v(\d+)$', s.strip()); return int(m.group(1))

    @staticmethod
    def imm(s):
        return int(s.strip(), 0)

    @staticmethod
    def bv(v):
        v = int(v)
        return '(0x%x#64)' % (v % (1 << 64))

    def target(self, s):
        m = re.match(r'^([0-9a-f]+) <', s.strip()); return self.addr2idx[int(m.group(1), 16)]

    @staticmethod
    def memop(s):
        m = re.match(r'^(-?\d+)?\((\w+)\)$', s.strip())
        return m.group(2), int(m.group(1) or 0)

    def translate(self, addr, text):
        parts = text.split(None, 1)
        op = parts[0]
        args = [a for a in re.split(r',(?![^(]*\))', parts[1].split('#')[0] if len(parts) > 1 else '')] if len(parts) > 1 else []
        args = [a.strip() for a in args if a.strip()]
        R, V = self.reg, self.vreg
        OPS2 = {'xor': 'xor', 'or': 'or', 'and': 'and', 'add': 'add', 'sub': 'sub', 'andn': 'andn'}
        OPSI = {'xori': 'xori', 'ori': 'ori', 'andi': 'andi', 'addi': 'addi', 'slli': 'slli', 'srli': 'srli', 'rori': 'rori'}
        if op in OPS2: return '.op %d %d %d .%s' % (R(args[0]), R(args[1]), R(args[2]), OPS2[op])
        if op in OPSI: return '.opi %d %d .%s %s' % (R(args[0]), R(args[1]), OPSI[op], self.bv(self.imm(args[2])))
        if op == 'li': return '.li %d %s' % (R(args[0]), self.bv(self.imm(args[1])))
        if op == 'mv': return '.mv %d %d' % (R(args[0]), R(args[1]))
        if op == 'not': return '.not %d %d' % (R(args[0]), R(args[1]))
        if op == 'nop': return '.nop'
        if op == 'ret': return '.ret'
        if op == 'auipc':
            rel = [r for r in self.reloc.get(addr, []) if r[0] == 'R_RISCV_PCREL_HI20']
            assert rel, 'auipc without relocation at %x' % addr
            sym = rel[0][1]
            m = re.match(r'^\.LRC(?:\+0x([0-9a-f]+))?$', sym)
            assert m, sym
            return '.lea %d ⟨4, %d⟩' % (R(args[0]), int(m.group(1) or '0', 16))
        if op == 'ld':
            base, off = self.memop(args[1]); return '.ld %d %d (%d)' % (R(args[0]), R(base), off)
        if op == 'sd':
            base, off = self.memop(args[1]); return '.sd %d %d (%d)' % (R(args[0]), R(base), off)
        if op in ('lbu', 'sb', 'vle8.v', 'vse8.v'): return '.unsupported "%s"' % op
        if op == 'beqz': return '.br .eq %d 0 %d' % (R(args[0]), self.target(args[1]))
        if op == 'bnez': return '.br .ne %d 0 %d' % (R(args[0]), self.target(args[1]))
        if op == 'beq': return '.br .eq %d %d %d' % (R(args[0]), R(args[1]), self.target(args[2]))
        if op == 'bne': return '.br .ne %d %d %d' % (R(args[0]), R(args[1]), self.target(args[2]))
        if op == 'bgeu': return '.br .geu %d %d %d' % (R(args[0]), R(args[1]), self.target(args[2]))
        if op == 'j': return '.j %d' % self.target(args[0])
        if op == 'vsetvli':
            if args[2:4] != ['e64', 'm1']: return '.unsupported "vsetvli %s"' % ' '.join(args[2:4])
            return '.vsetvli %d %d' % (R(args[0]), R(args[1]))
        VOPS = {'vxor.vv': 'xor', 'vand.vv': 'and', 'vor.vv': 'or', 'vandn.vv': 'andn'}
        if op in VOPS: return '.vop %d %d %d .%s' % (V(args[0]), V(args[1]), V(args[2]), VOPS[op])
        if op == 'vnot.v': return '.vnot %d %d' % (V(args[0]), V(args[1]))
        VSH = {'vsll': 'sll', 'vsrl': 'srl', 'vror': 'ror'}
        m = re.match(r'^(vsll|vsrl|vror)\.(vi|vx)$', op)
        if m:
            if m.group(2) == 'vi': return '.vshifti %d %d .%s %d' % (V(args[0]), V(args[1]), VSH[m.group(1)], self.imm(args[2]))
            return '.vshiftx %d %d .%s %d' % (V(args[0]), V(args[1]), VSH[m.group(1)], R(args[2]))
        if op == 'vxor.vx': return '.vxorx %d %d %d' % (V(args[0]), V(args[1]), R(args[2]))
        if op == 'vmv.v.i': return '.vmvi %d %s' % (V(args[0]), self.bv(self.imm(args[1])))
        if op == 'vmv.v.x': return '.vmvx %d %d' % (V(args[0]), R(args[1]))
        if op == 'vmv.v.v': return '.vmvv %d %d' % (V(args[0]), V(args[1]))
        m = re.match(r'^vlseg(\d)e64\.v$', op)
        if m:
            base, off = self.memop(args[1]); assert off == 0
            return '.vlseg %d %d %s' % (V(args[0]), R(base), m.group(1))
        m = re.match(r'^vsseg(\d)e64\.v$', op)
        if m:
            base, off = self.memop(args[1]); assert off == 0
            return '.vsseg %d %d %s' % (V(args[0]), R(base), m.group(1))
        raise ValueError('unhandled: %x %s' % (addr, text))

    def emit(self, ns, out):
        out.write('import Keccaktree.Asm.Riscv\n')
        out.write('/-! GENERATED by lean/asm2lean.py from %s (riscv64 objdump -d -r); do not edit. -/\n' % self.obj.split('/')[-1])
        out.write('namespace %s\nopen Keccaktree.Asm.Riscv\n\n' % ns)
        out.write('set_option maxRecDepth 100000 in\ndef prog : Array Instr := #[\n')
        for i, ins in enumerate(self.instrs):
            out.write('  %s%s  -- %d\n' % (ins, ',' if i + 1 < len(self.instrs) else '', i))
        out.write(']\n\n/-- The `.rodata` section (`.LRC`: the round constants), as 64-bit words. -/\ndef rodata : Array (BitVec 64) := #[\n')
        out.write(',\n'.join('  (0x%016x#64)' % w for w in self.rodata) + '\n]\n\n')
        out.write('def entry : Nat := %d\n\nend %s\n' % (self.entry, ns))


if __name__ == '__main__':
    isa, obj, func, ns = sys.argv[1:5]
    if isa == 'x86':
        X86(obj, func).emit(ns, sys.stdout)
    elif isa == 'arm':
        Arm(obj, func).emit(ns, sys.stdout)
    elif isa == 'riscv':
        Riscv(obj, func).emit(ns, sys.stdout)
    else:
        raise SystemExit('isa?')
