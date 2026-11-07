#!/usr/bin/env python3
"""Emit Tools/DiffCases/All.lean: the test-case programs by set name.   mkall.py <set>=<Module>:<isa> ..."""
import sys
sets = [a.split('=') for a in sys.argv[1:]]
out = ['import Keccaktree.Asm.Riscv']
out += ['import Tools.DiffCases.%s' % m.split(':')[0] for _, m in sets]
out += ['', 'namespace Tools.DiffCases', '',
        'inductive Prog where',
        '  | x86 (prog : Array Keccaktree.Asm.X86.Instr) (rodata : Array (BitVec 64)) (entries : Array Nat)',
        '  | arm (prog : Array Keccaktree.Asm.Arm.Instr) (rodata : Array (BitVec 64)) (entries : Array Nat)',
        '  | riscv (prog : Array Keccaktree.Asm.Riscv.Instr) (rodata : Array (BitVec 64)) (entries : Array Nat)',
        '', 'def find : String → Option Prog']
for name, m in sets:
    mod, isa = m.split(':')
    out.append('  | "%s" => some (.%s %s.prog %s.rodata %s.entries)' % (name, isa, mod, mod, mod))
out += ['  | _ => none', '', 'end Tools.DiffCases', '']
open('../Tools/DiffCases/All.lean', 'w').write('\n'.join(out))
