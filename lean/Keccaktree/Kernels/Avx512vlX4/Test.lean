import Keccaktree.Asm.Exec
import Keccaktree.Kernels.Avx512vlX4.Program
namespace Keccaktree.Kernels.Avx512vlX4
open Keccaktree.Asm.X86
-- (ok, err, instructions executed, tail-call pending)
#eval check prog rodata entry 0
#eval check prog rodata entry 4
#eval check prog rodata entry 2
#eval check prog rodata entry 3
#eval check prog rodata entry 8
#eval check prog rodata entry 11
#eval check prog rodata entry 1
#eval check prog rodata entry 5
end Keccaktree.Kernels.Avx512vlX4
