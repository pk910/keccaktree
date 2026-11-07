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
K=avx2_x4;      want "$@" && ISA=X86 gen avx2_x4 Avx2X4 4 4 0 4968 384 595 804 1016 1225 1437 1646 1858 2067 2279 2488 2700 2909 3121 3330 3542 3751 3963 4172 4384 4593 4822 4927
K=avx2_x8;      want "$@" && ISA=X86 gen avx2_x8 Avx2X8 8 4 0 10335 759 1212 1650 2091 2529 2970 3408 3849 4287 4728 5166 5607 6045 6486 6924 7365 7803 8244 8682 9123 9561 10051 10270
K=avx512vl_x4;  want "$@" && ISA=X86 gen avx512vl_x4 Avx512vlX4 4 4 0 2840 139 255 370 485 611 738 853 968 1094 1221 1336 1451 1577 1704 1819 1934 2060 2187 2302 2417 2543 2670 2785
K=avx512_x8;    want "$@" && ISA=X86 gen avx512_x8 Avx512X8 8 8 0 2856 147 263 378 493 619 746 861 976 1102 1229 1344 1459 1585 1712 1827 1942 2068 2195 2310 2425 2551 2678 2793
K=avx2_x2;      want "$@" && ISA=X86 gen avx2_x2 Avx2X2 2 4 0 3892 327 490 656 819 985 1148 1314 1477 1643 1806 1972 2135 2301 2464 2630 2793 2959 3122 3288 3451 3617 3774 3857
K=avx2_x5;      want "$@" && ISA=X86 gen avx2_x5 Avx2X5 5 4 0 8626 465 830 1197 1563 1930 2296 2663 3029 3396 3762 4129 4495 4862 5228 5595 5961 6328 6694 7061 7427 7794 8160 8527
K=avx2_x6;      want "$@" && ISA=X86 gen avx2_x6 Avx2X6 6 4 0 12507 650 1181 1714 2246 2779 3311 3844 4376 4909 5441 5974 6506 7039 7571 8104 8636 9169 9701 10234 10766 11299 11831 12364
K=avx2_x9;      want "$@" && ISA=X86 gen avx2_x9 Avx2X9 9 4 0 14174 764 1379 1982 2585 3188 3791 4394 4997 5600 6203 6806 7409 8012 8615 9218 9821 10424 11027 11630 12233 12836 13439 14020
K=avx2_x10;     want "$@" && ISA=X86 gen avx2_x10 Avx2X10 10 4 0 17930 929 1705 2469 3233 3997 4761 5525 6289 7053 7817 8581 9345 10109 10873 11637 12401 13165 13929 14693 15457 16221 16985 17743
K=avx512_x9;    want "$@" && ISA=X86 gen avx512_x9 Avx512X9 9 8 0 6520 336 608 879 1150 1432 1715 1986 2257 2539 2822 3093 3364 3646 3929 4200 4471 4753 5036 5307 5578 5860 6143 6414
K=x86_x1;       want "$@" && ISA=X86 gen x86_x1 X86X1 1 0 0 4290 291 476 658 844 1026 1212 1394 1580 1762 1948 2130 2316 2498 2684 2866 3052 3234 3420 3602 3788 3970 4168 4259
K=scalar_x1;    want "$@" && ISA=Arm gen scalar_x1 ScalarX1 1 0 0 2451 113 217 321 425 529 633 737 841 945 1049 1153 1257 1361 1465 1569 1673 1777 1881 1985 2089 2193 2297 2400
K=sha3_x2;      want "$@" && ISA=Arm gen sha3_x2 Sha3X2 2 2 0 1604 94 161 228 295 362 429 496 563 630 697 764 831 898 965 1032 1099 1166 1233 1300 1367 1434 1501 1568
K=neon_x2;      want "$@" && ISA=Arm gen neon_x2 NeonX2 2 2 0 3793 173 335 497 659 821 983 1145 1307 1469 1631 1793 1955 2117 2279 2441 2603 2765 2927 3089 3251 3413 3575 3737
K=sha3_x3;      want "$@" && ISA=Arm gen sha3_x3 Sha3X3 3 2 0 4553 226 419 612 805 998 1191 1384 1577 1770 1963 2156 2349 2542 2735 2928 3121 3314 3507 3700 3893 4086 4279 4462
K=sha3_x3r;    want "$@" && ISA=Arm gen sha3_x3r Sha3X3r 3 2 0 4642 $(seq23 213 197)
K=neon_x3;      want "$@" && ISA=Arm gen neon_x3 NeonX3 3 2 0 6237 278 544 810 1076 1342 1608 1874 2140 2406 2672 2938 3204 3470 3736 4002 4268 4534 4800 5066 5332 5598 5864 6134
K=rv64_x1;     want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa 2)" gen rv64_x1 Rv64X1 1 0 0 5406 $(seq23 290 228)
K=zbb_x1;      want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa 2)" gen zbb_x1 ZbbX1 1 0 0 3475 $(seq23 206 145)
for v in 2 4 8; do
  K=rvv_v$v;      want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa $v)" PROG_NS=Rvv gen rvv_v$v RvvV$v $v $v 0 5781 $(seq23 289 246)
  K=rvv_zvkb_v$v; want "$@" && ISA=Riscv ISA_EXPR="(Riscv.isa $v)" PROG_NS=RvvZvkb gen rvv_zvkb_v$v RvvZvkbV$v $v $v 0 3174 $(seq23 175 134)
done
true
