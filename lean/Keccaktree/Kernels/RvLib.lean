import Keccaktree.Kernels.RvLib2
import Keccaktree.Kernels.RvLib4
import Keccaktree.Kernels.RvLib8
/-!
# The RISC-V library, every kernel on any number of nodes

One table per vector length the RVV kernels are proved for: `vlmax = VLEN/64 ∈ {2, 4, 8}`
(VLEN 128, 256, 512).  The scalar kernels (`rv64_x1`, `zbb_x1`) have no `vsetvli` and are proved for
every `vlmax` (`Riscv.run_vlmax`).  **Coverage gap**: the dispatcher selects `rvv`/`rvv_zvkb` for every
VLEN ≥ 128; VLEN ≥ 1024 (`vlmax ≥ 16`) is not covered — the model's vector registers hold 8 lanes
(`State.v : Vector (Vector α 8) 32`), so `Riscv.isa vlmax` with `vlmax > 8` is not a faithful model and
no theorem is stated for it.  `lib<V>ch`: the same under any legal vector-length choice
(`Riscv.LegalVl`, RVV 1.0 §6.3), not only `vl = min(avl, VLMAX)`.
-/

