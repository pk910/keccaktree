#!/bin/bash
# Combined final axioms check in kt-int: for every top theorem of the final tree, `#print axioms`, run as
# four Lean files (ARM, x86, RISC-V, libraries+core; one lean process at a time, memory-gated), summarized
# by lean/axsum.py over all four outputs.  Output: /root/kt-int/axioms/Final_<g>.lean, out_Final_<g>.txt,
# final_axsum.txt, final_times.txt
export PATH=/root/.elan/bin:$PATH
cd /root/kt-int/lean; A=/root/kt-int/axioms; K=Keccaktree.Kernels
pr() { for t in "$@"; do echo "#print axioms $t"; done; }
# ---- ARM
{ for k in ScalarX1 Sha3X2 NeonX2 Sha3X3 Sha3X3r NeonX3; do echo "import $K.$k.All"; echo "import $K.$k.InPlaceAll"; done
  pr $K.ScalarX1.All.scalar_x1_all $K.ScalarX1.All.norm_thm $K.ScalarX1.All.kernel
  for k in Sha3X2 NeonX2 Sha3X3 Sha3X3r NeonX3; do pr $K.$k.All.all $K.$k.All.norm_thm $K.$k.All.kernel; done
  for k in ScalarX1 Sha3X2 NeonX2 Sha3X3 Sha3X3r NeonX3; do pr $K.$k.InPlaceAll.access_thm $K.$k.InPlaceAll.kernelAl; done
} > $A/Final_arm.lean
# ---- x86
X86="X86X1 Avx2X2 Avx2X4 Avx2X5 Avx2X6 Avx2X8 Avx2X9 Avx2X10 Avx512vlX4 Avx512vlX4d Avx512X8 Avx512X8d Avx512X9 Avx512X9d"
{ for k in $X86; do echo "import $K.$k.Lib"; echo "import $K.$k.InPlaceAll"; done
  for k in Avx2X4 Avx2X10; do echo "import $K.$k.LibV"; echo "import $K.$k.InPlaceAllV"; done
  pr $K.X86X1.All.x86_x1_all $K.X86X1.Lib.norm_thm
  for k in $X86; do [ $k = X86X1 ] || pr $K.$k.All.norm_thm; pr $K.$k.Lib.kernel $K.$k.InPlaceAll.access_thm $K.$k.InPlaceAll.kernelAl; done
  for k in Avx2X4 Avx2X10; do pr $K.$k.AllV.norm_thm $K.$k.LibV.kernel $K.$k.InPlaceAllV.access_thm $K.$k.InPlaceAllV.kernelAl; done
} > $A/Final_x86.lean
# ---- RISC-V
{ for k in Rv64X1 ZbbX1; do echo "import $K.$k.All"; echo "import $K.$k.AllU"; echo "import $K.$k.InPlaceAll"; done
  for V in 2 4 8; do for k in RvvV$V RvvZvkbV$V; do echo "import $K.$k.AllUM"; echo "import $K.$k.InPlaceAll"; done; done
  for k in Rv64X1:rv64_x1 ZbbX1:zbb_x1; do ns=${k%%:*}; s=${k##*:}
    pr $K.$ns.All.${s}_all $K.$ns.All.norm_thm $K.$ns.All.kernel $K.$ns.All.kernel_ch $K.$ns.AllU.${s}_allU $K.$ns.AllU.kernelU \
       $K.$ns.AllU.kernelU_ch $K.$ns.InPlaceAll.access_thm $K.$ns.InPlaceAll.kernelAl; done
  for V in 2 4 8; do for k in RvvV$V RvvZvkbV$V; do
    pr $K.$k.All.all $K.$k.All.all_ch $K.$k.All.norm_thm $K.$k.All.kernel $K.$k.All.kernel_ch $K.$k.AllUM.norm_thmU $K.$k.AllUM.kernelU \
       $K.$k.InPlaceAll.access_thm $K.$k.InPlaceAll.kernelAl; done; done
} > $A/Final_rv.lean
# ---- library tables and core
{ for m in ArmLib ArmLibInPlace X86Lib X86LibInPlace RvLib RvLibUV RvLibU RvLibInPlace; do echo "import $K.$m"; done
  echo "import Keccaktree.Dispatch"
  pr $K.ArmLib.lib_arm_all $K.ArmLibInPlace.lib_inplace_arm_all $K.X86Lib.lib_x86_all $K.X86LibInPlace.lib_inplace_x86_all \
     $K.RvLib.lib2 $K.RvLib.lib2ch $K.RvLib.lib4 $K.RvLib.lib4ch $K.RvLib.lib8 $K.RvLib.lib8ch $K.RvLibU.libU $K.RvLibU.libU_ch \
     $K.RvLibUV.lib2U $K.RvLibUV.lib4U $K.RvLibUV.lib8U $K.RvLibInPlace.lib_inplace2 $K.RvLibInPlace.lib_inplace4 $K.RvLibInPlace.lib_inplace8 \
     Keccaktree.Asm.LibTable.lib_x86 Keccaktree.Asm.LibTable.lib_arm Keccaktree.Asm.LibTable.lib_rv \
     Keccaktree.Dispatch.hash_x86 Keccaktree.Dispatch.hash_x86_reachable Keccaktree.Dispatch.hash_arm Keccaktree.Dispatch.hash_rv
} > $A/Final_lib.lean
: > $A/final_times.txt
for g in arm x86 rv lib; do
  echo "Final_$g: $(grep -c '#print' $A/Final_$g.lean) theorems"
  /root/kt-int-gate.sh
  /usr/bin/time -f "Final_$g %e s %M KB rc=%x" lake env lean $A/Final_$g.lean > $A/out_Final_$g.txt 2>> $A/final_times.txt
done
cat $A/final_times.txt
python3 /root/kt-int/lean/axsum.py $A/out_Final_arm.txt $A/out_Final_x86.txt $A/out_Final_rv.txt $A/out_Final_lib.txt > $A/final_axsum.txt
echo "axsum rc=$?"; tail -1 $A/final_axsum.txt
