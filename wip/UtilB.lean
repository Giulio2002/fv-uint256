import Janus
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB

/-! Helper lemmas for family B (division, modular arithmetic, iterative numerics). -/

namespace Fv256.B

theorem clz_cases (v : Nat) (h : v < 2 ^ 64) : v = 0 ∨ Janus.Arm64.clzNat 64 v < 64 := by
  by_cases hv : v = 0
  · exact Or.inl hv
  · refine Or.inr ?_
    have := Fv256.Util.clz_bl 64 v h
    have h2 : 0 < Fv256.Spec.bitLen v := by
      unfold Fv256.Spec.bitLen; rw [if_neg hv]; omega
    omega

end Fv256.B
