import Fv256.Amd64.SqrtMainL
import Fv256.Amd64.SqrtSumL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SqrtLib

/-- `Sqrt` as a library summary over `Fv256.SqrtProg.program`: the number at `RAX` becomes the integer square root of the
number at `RBX` (`RAX` and `RBX` equal or disjoint), window `[RSP-0x1f0, RSP+0x18)`. -/
theorem sqrt_summary : Summary Fv256.SqrtProg.program sqrtEntry SPre SPost := by
  intro s hpc hpre
  by_cases hb : s.mem.readLE ((s.regs 3).toNat + 8) 8 ≠ 0 ∨ s.mem.readLE ((s.regs 3).toNat + 16) 8 ≠ 0 ∨
      s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0
  · exact sqrt_big s hpc ⟨hpre, hb⟩
  · exact sqrt_small s hpc ⟨hpre, by omega, by omega, by omega⟩

end Fv256.Amd64.SqrtLib
