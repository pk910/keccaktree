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
        for addr, text, reloc, end in raw:
            self.instrs.append(self.translate(addr, text, reloc, end))
        self.check_flags()

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
                    break
                if op in self.FLAG_BAD or op in ('.jmp', '.jcc', '.call', '.ret', '.tailcall', '.repmovsb') or j in targets:
                    raise ValueError('flags of instruction %d (%s) used by jcc %d are not modelled' % (j, self.instrs[j], i))
                j -= 1
            else:
                raise ValueError('jcc %d without a flag setter' % i)

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
            return '.kmovw %d %s' % (int(args[0][1:]), self.memop(args[1], reloc, end))
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
                b, o, wb = self.memop(args[1]); assert wb == 0
                return '.ldr %s %d (%d)' % (self.lreg(args[0]), b, o)
            m = re.match(r'^([0-9a-f]+) <', args[1]); a = int(m.group(1), 16)
            r = self.lreg(args[0])
            if r.startswith('(.q'): return '.ldrlit %s (0x%016x#64) (0x%016x#64)' % (r, self.word64(a), self.word64(a + 8))
            return '.ldrlit %s (0x%016x#64) (0#64)' % (r, self.word64(a))
        if op == 'str':
            b, o, wb = self.memop(args[1]); assert wb == 0
            return '.str %s %d (%d)' % (self.lreg(args[0]), b, o)
        if op in ('ldp', 'stp'):
            b, o, wb = self.memop(args[2])
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
