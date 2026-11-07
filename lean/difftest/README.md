# Differential instruction tests (model + translator vs. hardware)

Every instruction form the Lean models (`Keccaktree/Asm/{X86,Arm,Riscv}.lean`) implement is executed
on random states (a) on the real CPU / under an emulator and (b) in the Lean model, and the final
states are compared.  The model side goes through the real translator: test snippets are assembled
by the real toolchain, disassembled by `objdump -d -r` and translated by `../asm2lean.py` exactly as
the kernels are (`mkcases.py`), then compiled into `difftool` (`../Tools/Diff.lean`).

Test snippets (`c_<j>`, one function each, ending in a tail jump to `kt_back`):
* every distinct non-control instruction of the kernels (x86: 4.6k; rip-relative constants are
  redirected into the test constants `kt_ro` / `kt_dat`),
* random instances of every modelled form (`t_*` templates: registers, widths, immediates, memory
  operands, broadcasts, masks, misaligned addresses),
* control templates: flag setter + `jcc` (local and to another function), `jmp`, `call`/`ret`.

## State format (states.txt, hw.txt, model.txt)
```
C <snippet> <seed hex>     (outputs: C <case number>)
G <i> <hex> [P]            general register i; P: a pointer, (region << 56) + offset
V <i> <hex> x8             vector register lanes (64-bit)
K <i> <dec>                AVX-512 mask register
F <zf> <cf> <nf> <vf>      flags
L <vl>                     RVV vector length
M <r> <q> <hex> [P]        memory word q of region r (inputs: overrides of the default
                           mix(seed, r, q); outputs: words that changed)
X <err> <halted> <pc>      model only
W <exit>                   1 = kt_back, 2 = kt_back2 (x86 control templates)
S <signal>                 hardware fault
E                          end of the state
```
Regions 1..3 (input, output, stack) are 32 KiB buffers (`W = 4096` words) on the hardware side,
region 4 is the constants.  Hardware and model words are equal modulo the region encoding
(`compare.py`).  Cases where the model reports `err` are not compared (the model claims nothing
there; the kernel proofs show `err = false`); their number is reported per form.

## Running (remote)
```
bash run_x86.sh /root/kt-diff/x1 <seed> [states per kernel instruction] [instances per template]
```
x86: VEX/scalar forms natively (AVX2 host), EVEX forms under Intel SDE (`-spr`).
