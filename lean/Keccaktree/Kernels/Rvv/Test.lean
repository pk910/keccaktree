import Keccaktree.Asm.Riscv
import Keccaktree.Kernels.Rvv.Program
namespace Keccaktree.Kernels.Rvv
open Keccaktree.Asm.Riscv
#eval check 2 prog rodata entry 0
#eval check 2 prog rodata entry 1
#eval check 2 prog rodata entry 2
#eval check 2 prog rodata entry 3
#eval check 2 prog rodata entry 5
#eval check 4 prog rodata entry 1
#eval check 4 prog rodata entry 4
#eval check 4 prog rodata entry 7
#eval check 8 prog rodata entry 3
#eval check 8 prog rodata entry 8
#eval check 8 prog rodata entry 11
-- the model must compute the expected digests (CI fails otherwise)
#guard (check 2 prog rodata entry 0).1
#guard (check 2 prog rodata entry 1).1
#guard (check 2 prog rodata entry 2).1
#guard (check 2 prog rodata entry 3).1
#guard (check 2 prog rodata entry 5).1
#guard (check 4 prog rodata entry 1).1
#guard (check 4 prog rodata entry 4).1
#guard (check 4 prog rodata entry 7).1
#guard (check 8 prog rodata entry 3).1
#guard (check 8 prog rodata entry 8).1
#guard (check 8 prog rodata entry 11).1
end Keccaktree.Kernels.Rvv
