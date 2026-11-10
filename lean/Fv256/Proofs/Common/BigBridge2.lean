import Fv256.Spec.MustFromBig

/-!
# Bridge: when does `MustFromBig` panic (`Spec.mustFromBig`), in the limb-count form the proofs use
-/

namespace Fv256.Proofs.Big

theorem isSome_mustFromBig (b : Int) (n : Nat) : (Fv256.Spec.mustFromBig b n).isSome = true ↔ n ≤ 4 := by
  unfold Fv256.Spec.mustFromBig Fv256.Spec.setFromBigOverflow
  by_cases h : 4 < n <;> simp [h] <;> omega

theorem isNone_mustFromBig (b : Int) (n : Nat) : (Fv256.Spec.mustFromBig b n).isNone = true ↔ 4 < n := by
  unfold Fv256.Spec.mustFromBig Fv256.Spec.setFromBigOverflow
  by_cases h : 4 < n <;> simp [h]

end Fv256.Proofs.Big
