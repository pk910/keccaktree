import Keccaktree.Kernels.Avx2X4.Test
import Keccaktree.Kernels.NeonX3.Test
import Keccaktree.Kernels.X86X1.Test
import Keccaktree.Kernels.Avx512X9.Test
import Keccaktree.Kernels.Avx2X10.Test
import Keccaktree.Kernels.Avx2X9.Test
import Keccaktree.Kernels.Avx2X6.Test
import Keccaktree.Kernels.Avx2X5.Test
import Keccaktree.Kernels.Avx2X2.Test
import Keccaktree.Kernels.Avx2X8.Test
import Keccaktree.Kernels.Avx512vlX4.Test
import Keccaktree.Kernels.Avx512X8.Test
import Keccaktree.Kernels.NeonX2.Test
import Keccaktree.Kernels.Sha3X2.Test
import Keccaktree.Kernels.Sha3X3.Test
import Keccaktree.Kernels.Sha3X3r.Test
import Keccaktree.Kernels.ScalarX1.Test
import Keccaktree.Kernels.Rv64X1.Test
import Keccaktree.Kernels.ZbbX1.Test
import Keccaktree.Kernels.Rvv.Test
import Keccaktree.Kernels.RvvZvkb.Test
/-! The thirteen assembly kernels as Lean programs (generated from the object code), with their
executable test harnesses (`#eval check …` runs every kernel model on the C test vectors). -/
