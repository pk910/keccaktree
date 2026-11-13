import Keccaktree.Asm.Exec
import Keccaktree.Kernels.X86X1.Program
namespace Keccaktree.Kernels.X86X1
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
-- the model must compute the expected digests (CI fails otherwise)
#guard (check prog rodata entry 0).1
#guard (check prog rodata entry 4).1
#guard (check prog rodata entry 2).1
#guard (check prog rodata entry 3).1
#guard (check prog rodata entry 8).1
#guard (check prog rodata entry 11).1
#guard (check prog rodata entry 1).1
#guard (check prog rodata entry 5).1
end Keccaktree.Kernels.X86X1
