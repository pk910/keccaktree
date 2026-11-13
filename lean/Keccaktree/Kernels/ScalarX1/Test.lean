import Keccaktree.Asm.Arm
import Keccaktree.Kernels.ScalarX1.Program
namespace Keccaktree.Kernels.ScalarX1
open Keccaktree.Asm.Arm
#eval check prog rodata entry 0
#eval check prog rodata entry 1
#eval check prog rodata entry 2
#eval check prog rodata entry 3
#eval check prog rodata entry 5
#eval check prog rodata entry 7
-- the model must compute the expected digests (CI fails otherwise)
#guard (check prog rodata entry 0).1
#guard (check prog rodata entry 1).1
#guard (check prog rodata entry 2).1
#guard (check prog rodata entry 3).1
#guard (check prog rodata entry 5).1
#guard (check prog rodata entry 7).1
end Keccaktree.Kernels.ScalarX1
