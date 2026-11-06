import Keccaktree.Asm.Riscv
import Keccaktree.Kernels.Rv64X1.Program
namespace Keccaktree.Kernels.Rv64X1
open Keccaktree.Asm.Riscv
#eval check 2 prog rodata entry 0
#eval check 2 prog rodata entry 1
#eval check 2 prog rodata entry 2
#eval check 2 prog rodata entry 3
end Keccaktree.Kernels.Rv64X1
