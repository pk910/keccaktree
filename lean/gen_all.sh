#!/bin/bash
# Generate the slice proofs of every kernel (kttool must be built: `lake build kttool`).
# entry_t = 0 (the batch starts at the kernel entry: the entry-state theorems need the first cut to be the entry state),
# end_t = scan line of the final halting `ret` + 1 (the last slice includes it).
# Usage: gen_all.sh [kernel ...]   (default: all); env SLICES/ONLY_NODE/BATCH pass through.
set -e
cd "$(dirname "$0")"
seq23() { python3 -c "print(' '.join(str($1+$2*(r-1)) for r in range(1,24)))"; }
gen() { # name ns count lanes entry end cuts... [env...]
  local name=$1 ns=$2; shift 2
  mkdir -p "Keccaktree/Kernels/$ns/Gen"
  echo "== $name"
  OUTDIR="Keccaktree/Kernels/$ns/Gen" python3 gen_kernel_proof.py "$name" "$ns" "$@"
}
want() { [ $# -eq 0 ] && return 0; for k in "$@"; do [ "$k" = "$K" ] && return 0; done; return 1; }
K=avx2_x4;     want "$@" && ISA=X86 gen avx2_x4 Avx2X4 4 4 0 4965 258 468 677 889 1098 1310 1519 1731 1940 2152 2361 2573 2782 2994 3203 3415 3624 3836 4045 4257 4466 4678 4887
K=avx2_x8;     want "$@" && ISA=X86 gen avx2_x8 Avx2X8 8 4 0 10327 509 973 1411 1852 2290 2731 3169 3610 4048 4489 4927 5368 5806 6247 6685 7126 7564 8005 8443 8884 9322 9763 10201
K=avx512vl_x4; want "$@" && ISA=X86 gen avx512vl_x4 Avx512vlX4 4 4 0 2717 $(seq23 135 115)
K=avx512_x8;   want "$@" && ISA=X86 gen avx512_x8 Avx512X8 8 8 0 2735 $(seq23 143 115)
K=scalar_x1;   want "$@" && ISA=Arm gen scalar_x1 ScalarX1 1 0 0 2502 $(seq23 112 106)
K=sha3_x2;     want "$@" && ISA=Arm gen sha3_x2 Sha3X2 2 2 0 1604 $(seq23 94 67)
K=neon_x2;     want "$@" && ISA=Arm gen neon_x2 NeonX2 2 2 0 3751 $(seq23 173 160)
K=sha3_x3;     want "$@" && ISA=Arm gen sha3_x3 Sha3X3 3 2 0 4561 $(seq23 226 193)
K=sha3_x3r;    want "$@" && ISA=Arm gen sha3_x3r Sha3X3r 3 2 0 4642 $(seq23 213 197)
K=rv64_x1;     want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa 2)" gen rv64_x1 Rv64X1 1 0 0 5406 $(seq23 290 228)
K=zbb_x1;      want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa 2)" gen zbb_x1 ZbbX1 1 0 0 3475 $(seq23 206 145)
for v in 2 4 8; do
  K=rvv_v$v;      want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa $v)" PROG_NS=Rvv gen rvv_v$v RvvV$v $v $v 0 5781 $(seq23 289 246)
  K=rvv_zvkb_v$v; want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa $v)" PROG_NS=RvvZvkb gen rvv_zvkb_v$v RvvZvkbV$v $v $v 0 3174 $(seq23 175 134)
done
true
