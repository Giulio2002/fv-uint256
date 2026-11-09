import Fv256.Proofs.Amd64.R4Reduce

/-!
# `(*Int).reduce4` (amd64) as a library summary over `Fv256.ReduceProg` (Extracted-free)

`reduce4_summary`: for every state at the entry of `uint256.reduce4` satisfying `R4Pre` (buffers, stack window, `m` with a nonzero top limb,
`mu` in the `RecipWeak` window of `⌊(2^512-1)/m⌋`), the call returns and `R4Post` holds: `z = x % m`, frame/registers preserved.
The proof is the segment composition in `R4Reduce.lean` (phase A, the generated segments `C_1cd_4ac`, the borrow branch, the final
`while r >= m` loop) with the Barrett arithmetic of `R4Arith.lean` (`MulModMath.reduce_value`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.Reduce4

theorem reduce4_summary : R4Summary := fun s hpc hpre =>
  Fv256.Amd64.R4Seg.reduce4_machine s hpc hpre

end Fv256.Amd64.Reduce4
