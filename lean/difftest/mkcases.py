#!/usr/bin/env python3
"""Translate a test-case object with the real translator (asm2lean.py) and emit the Lean module.

    mkcases.py <isa> <cases.o> <ModuleName> <out.lean> <instrs.json> [nsnips]

The module `Tools.DiffCases.<ModuleName>` holds `prog`, `rodata` (exactly as asm2lean emits
them for a kernel) and `entries` (instruction index of snippet `c_<j>`).  instrs.json records the
translated instruction of every index and its object address (for the comparator)."""
import io
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import asm2lean  # noqa: E402

isa, obj, mod, out, js = sys.argv[1:6]
cls = {'x86': asm2lean.X86, 'arm': asm2lean.Arm, 'riscv': asm2lean.Riscv}[isa]
tr = cls(obj, 'c_0')
buf = io.StringIO()
tr.emit('Tools.DiffCases.' + mod, buf)
src = buf.getvalue()
objdump = {'x86': 'objdump', 'arm': 'aarch64-linux-gnu-objdump', 'riscv': 'riscv64-linux-gnu-objdump'}[isa]
syms = {}
for ln in subprocess.run([objdump, '-t', obj], capture_output=True, text=True, check=True).stdout.splitlines():
    m = re.match(r'^([0-9a-f]+) .*\.text\s+[0-9a-f]+\s+(c_\d+)$', ln)
    if m:
        syms[int(m.group(2)[2:])] = int(m.group(1), 16)
n = max(syms) + 1
entries = [tr.addr2idx[syms[j]] for j in range(n)]
idx2addr = {i: a for a, i in tr.addr2idx.items()}
src = src.replace('end Tools.DiffCases.' + mod,
                  'set_option maxRecDepth 100000 in\ndef entries : Array Nat := #[%s]\n\nend Tools.DiffCases.%s' % (', '.join(map(str, entries)), mod))
open(out, 'w').write(src)
json.dump({'instrs': tr.instrs, 'addr': [idx2addr[i] for i in range(len(tr.instrs))], 'entries': entries}, open(js, 'w'))
print(mod, len(tr.instrs), 'instructions', n, 'snippets')
