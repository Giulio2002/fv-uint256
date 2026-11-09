import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.SpecB2

/-! Signed-remainder case splits for arm64 `SMod` (companion of `SDivLemmas`). -/

namespace Fv256.Arm64.SModLemmas

theorem sm_pp (X Y : Nat) (hx : X < 2 ^ 255) (hy : Y < 2 ^ 255) :
    Fv256.B.smodSpec X Y = Fv256.B.modSpec X Y := by
  unfold Fv256.B.smodSpec Fv256.Spec.abs
  rw [if_neg (by omega), if_pos hx, if_pos hy]

theorem sm_pn (X Y : Nat) (hx : X < 2 ^ 255) (hy : 2 ^ 255 ≤ Y) :
    Fv256.B.smodSpec X Y = Fv256.B.modSpec X (Fv256.Spec.neg Y) := by
  unfold Fv256.B.smodSpec Fv256.Spec.abs
  rw [if_neg (by omega), if_pos hx, if_neg (by omega)]
  rfl

theorem sm_np (X Y : Nat) (hx : 2 ^ 255 ≤ X) (hy : Y < 2 ^ 255) :
    Fv256.B.smodSpec X Y = Fv256.Spec.neg (Fv256.B.modSpec (Fv256.Spec.neg X) Y) := by
  unfold Fv256.B.smodSpec Fv256.Spec.abs
  rw [if_pos hx, if_neg (by omega), if_pos hy]
  rfl

theorem sm_nn (X Y : Nat) (hx : 2 ^ 255 ≤ X) (hy : 2 ^ 255 ≤ Y) :
    Fv256.B.smodSpec X Y = Fv256.Spec.neg (Fv256.B.modSpec (Fv256.Spec.neg X) (Fv256.Spec.neg Y)) := by
  unfold Fv256.B.smodSpec Fv256.Spec.abs
  rw [if_pos hx, if_neg (by omega), if_neg (by omega)]
  rfl

end Fv256.Arm64.SModLemmas
