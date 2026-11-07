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
rm -rf $T; exit $fail
