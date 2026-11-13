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
K=avx2_x4;      want "$@" && ISA=X86 gen avx2_x4 Avx2X4 4 4 0 4968 258 468 677 889 1098 1310 1519 1731 1940 2152 2361 2573 2782 2994 3203 3415 3624 3836 4045 4257 4466 4678 4887
K=avx2_x8;      want "$@" && ISA=X86 gen avx2_x8 Avx2X8 8 4 0 10335 514 978 1416 1857 2295 2736 3174 3615 4053 4494 4932 5373 5811 6252 6690 7131 7569 8010 8448 8889 9327 9768 10206
K=avx512vl_x4;  want "$@" && ISA=X86 gen avx512vl_x4 Avx512vlX4 4 4 0 2840 127 244 359 474 589 727 842 957 1072 1210 1325 1440 1555 1693 1808 1923 2038 2176 2291 2406 2521 2659 2774
K=avx512_x8;    want "$@" && ISA=X86 gen avx512_x8 Avx512X8 8 8 0 2856 135 252 367 482 597 735 850 965 1080 1218 1333 1448 1563 1701 1816 1931 2046 2184 2299 2414 2529 2667 2782
K=avx2_x2;      want "$@" && ISA=X86 gen avx2_x2 Avx2X2 2 4 0 3892 204 367 533 696 862 1025 1191 1354 1520 1683 1849 2012 2178 2341 2507 2670 2836 2999 3165 3328 3494 3657 3823
K=avx2_x5;      want "$@" && ISA=X86 gen avx2_x5 Avx2X5 5 4 0 8626 440 806 1171 1539 1904 2272 2637 3005 3370 3738 4103 4471 4836 5204 5569 5937 6302 6670 7035 7403 7768 8136 8501
K=avx2_x6;      want "$@" && ISA=X86 gen avx2_x6 Avx2X6 6 4 0 12507 633 1165 1696 2230 2761 3295 3826 4360 4891 5425 5956 6490 7021 7555 8086 8620 9151 9685 10216 10750 11281 11815 12346
K=avx2_x9;      want "$@" && ISA=X86 gen avx2_x9 Avx2X9 9 4 0 14174 707 1334 1937 2540 3143 3746 4349 4952 5555 6158 6761 7364 7967 8570 9173 9776 10379 10982 11585 12188 12791 13394 13997
K=avx2_x10;     want "$@" && ISA=X86 gen avx2_x10 Avx2X10 10 4 0 17930 890 1678 2442 3206 3970 4734 5498 6262 7026 7790 8554 9318 10082 10846 11610 12374 13138 13902 14666 15430 16194 16958 17722
K=avx512_x9;    want "$@" && ISA=X86 gen avx512_x9 Avx512X9 9 8 0 6520 321 594 865 1136 1407 1701 1972 2243 2514 2808 3079 3350 3621 3915 4186 4457 4728 5022 5293 5564 5835 6129 6400
K=x86_x1;       want "$@" && ISA=X86 gen x86_x1 X86X1 1 0 0 4290 184 368 550 736 918 1104 1286 1472 1654 1840 2022 2208 2390 2576 2758 2944 3126 3312 3494 3680 3862 4048 4230
K=scalar_x1;    want "$@" && ISA=Arm gen scalar_x1 ScalarX1 1 0 0 2451 102 206 310 414 518 622 726 830 934 1038 1142 1246 1350 1454 1558 1662 1766 1870 1974 2078 2182 2286 2390
K=sha3_x2;      want "$@" && ISA=Arm gen sha3_x2 Sha3X2 2 2 0 1604 87 154 221 288 355 422 489 556 623 690 757 824 891 958 1025 1092 1159 1226 1293 1360 1427 1494 1561
K=neon_x2;      want "$@" && ISA=Arm gen neon_x2 NeonX2 2 2 0 3793 155 317 479 641 803 965 1127 1289 1451 1613 1775 1937 2099 2261 2423 2585 2747 2909 3071 3233 3395 3557 3719
K=sha3_x3;      want "$@" && ISA=Arm gen sha3_x3 Sha3X3 3 2 0 4553 210 403 596 789 982 1175 1368 1561 1754 1947 2140 2333 2526 2719 2912 3105 3298 3491 3684 3877 4070 4263 4456
K=sha3_x3r;    want "$@" && ISA=Arm gen sha3_x3r Sha3X3r 3 2 0 4642 $(seq23 213 197)
K=neon_x3;      want "$@" && ISA=Arm gen neon_x3 NeonX3 3 2 0 6237 254 520 786 1052 1318 1584 1850 2116 2382 2648 2914 3180 3446 3712 3978 4244 4510 4776 5042 5308 5574 5840 6106
K=rv64_x1;     want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa 2)" gen rv64_x1 Rv64X1 1 0 0 5406 $(seq23 290 228)
K=zbb_x1;      want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa 2)" gen zbb_x1 ZbbX1 1 0 0 3475 $(seq23 206 145)
for v in 2 4 8; do
  K=rvv_v$v;      want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa $v)" PROG_NS=Rvv gen rvv_v$v RvvV$v $v $v 0 5781 $(seq23 289 246)
  K=rvv_zvkb_v$v; want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa $v)" PROG_NS=RvvZvkb gen rvv_zvkb_v$v RvvZvkbV$v $v $v 0 3174 $(seq23 175 134)
done
true
