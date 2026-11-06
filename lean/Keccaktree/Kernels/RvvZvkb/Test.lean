import Keccaktree.Asm.Riscv
import Keccaktree.Kernels.RvvZvkb.Program
namespace Keccaktree.Kernels.RvvZvkb
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
end Keccaktree.Kernels.RvvZvkb
