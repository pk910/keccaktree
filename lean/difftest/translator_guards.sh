#!/bin/bash
# Negative tests: asm2lean.py must refuse instruction uses outside the model's domain.
HERE=$(cd "$(dirname "$0")" && pwd); T=$(mktemp -d); fail=0
t() { # name, expected error substring, asm body
  printf '.intel_syntax noprefix\n.text\n.globl f\nf:\n%b\n' "$3" > $T/t.S
  gcc -c $T/t.S -o $T/t.o 2>$T/as.err || { echo "ASM FAIL $1: $(cat $T/as.err)"; fail=1; return; }
  if python3 -I "$HERE/../asm2lean.py" x86 $T/t.o f N >/dev/null 2>$T/err; then echo "NOT REJECTED: $1"; fail=1
  elif grep -q "$2" $T/err; then echo "rejected: $1"; else echo "WRONG ERROR $1: $(tail -1 $T/err)"; fail=1; fi
}
ok() { printf '.intel_syntax noprefix\n.text\n.globl f\nf:\n%b\n' "$2" > $T/t.S; gcc -c $T/t.S -o $T/t.o
  if python3 -I "$HERE/../asm2lean.py" x86 $T/t.o f N >/dev/null 2>$T/err; then echo "accepted: $1"; else echo "WRONGLY REJECTED $1: $(tail -1 $T/err)"; fail=1; fi; }
t "cmp negative imm" "negative immediate" "cmp rdx, -1\n je 1f\n1: ret"
t "sub negative imm" "negative immediate" "sub rdx, -8\n ret"
t "kmovw base register" "kmovw" "kmovw k1, WORD PTR [rsi]\n ret"
t "kmovw crossing a word" "kmovw" "kmovw k1, WORD PTR [rip+x+7]\n ret\n.section .rodata\nx: .quad 1, 2"
t "32-bit read at entry" "upper half" "dec ecx\n ret"
t "32-bit read after 64-bit write" "upper half" "mov ecx, 3\n mov rcx, rdx\n cmp ecx, 2\n ret"
t "32-bit register move" "not modelled" "mov eax, ebx\n ret"
t "32-bit add" "not modelled" "add eax, 1\n ret"
t "vector after vzeroupper" "after vzeroupper" "vzeroupper\n vpxor ymm0, ymm0, ymm1\n ret"
t "vector after vzeroupper (branch)" "after vzeroupper" "vzeroupper\n test rdx, rdx\n je 1f\n ret\n1: vmovdqu ymm0, ymm1\n ret"
t "32-bit dec of zero" "may be zero" "xor ecx, ecx\n dec ecx\n ret"
t "flags of sub on rsp" "possible pointer" "sub rsp, 8\n je 1f\n1: ret"
ok "32-bit loop counter" "mov ecx, 0xb\n1: dec ecx\n jne 1b\n ret"
ok "32-bit selector" "xor eax, eax\n test eax, eax\n je 1f\n mov eax, 2\n1: cmp eax, 2\n ret"
ok "vzeroupper then ret" "vzeroupper\n pop rbp\n ret"
rv() { # name, expected error substring (or "OK"), asm body
  printf '.option norvc\n.attribute arch, "rv64gcv"\n.text\n.globl f\nf:\n%b\n.section .rodata\n.LRC: .quad 1, 2\n' "$3" > $T/r.S
  riscv64-linux-gnu-gcc -c $T/r.S -o $T/r.o 2>$T/as.err || { echo "ASM FAIL $1: $(cat $T/as.err)"; fail=1; return; }
  if python3 -I "$HERE/../asm2lean.py" riscv $T/r.o f N >/dev/null 2>$T/err; then
    [ "$2" = OK ] && echo "accepted: $1" || { echo "NOT REJECTED: $1"; fail=1; }
  elif [ "$2" != OK ] && grep -q "$2" $T/err; then echo "rejected: $1"; else echo "WRONG $1: $(tail -1 $T/err)"; fail=1; fi
}
rv "riscv vector shift by a register" "not a constant" " vsetvli t0, a2, e64, m1, ta, ma\n vsrl.vx v1, v2, t4\n ret"
rv "riscv vector shift by li 64" "not a constant" " vsetvli t0, a2, e64, m1, ta, ma\n li t4, 64\n vsrl.vx v1, v2, t4\n ret"
rv "riscv vector shift by li 63" OK " vsetvli t0, a2, e64, m1, ta, ma\n li t4, 63\n vsrl.vx v1, v2, t4\n ret"
rv "riscv auipc not paired" "auipc" "1: auipc t1, %pcrel_hi(.LRC)\n addi t2, t1, %pcrel_lo(1b)\n ret"
rv "riscv la pair" OK "1: auipc t1, %pcrel_hi(.LRC)\n addi t1, t1, %pcrel_lo(1b)\n ld t2, 0(t1)\n ret"
arm() {
  printf '.arch armv8.2-a+sha3\n.text\n.globl f\n.type f, %%function\nf:\n%b\n' "$3" > $T/a.S
  aarch64-linux-gnu-gcc -c $T/a.S -o $T/a.o 2>$T/as.err || { echo "ASM FAIL $1: $(cat $T/as.err)"; fail=1; return; }
  if python3 -I "$HERE/../asm2lean.py" arm $T/a.o f N >/dev/null 2>$T/err; then
    [ "$2" = OK ] && echo "accepted: $1" || { echo "NOT REJECTED: $1"; fail=1; }
  elif [ "$2" != OK ] && grep -q "$2" $T/err; then echo "rejected: $1"; else echo "WRONG $1: $(tail -1 $T/err)"; fail=1; fi
}
arm "arm vector use after ldp d" "d-register load" " ldp d8, d9, [sp], #16\n eor v0.16b, v8.16b, v9.16b\n ret"
arm "arm ldp d in the epilogue" OK " ldp d8, d9, [sp, #16]\n ldp x29, x30, [sp], #32\n ret"
rm -rf $T; exit $fail
