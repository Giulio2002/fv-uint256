import Janus
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.SpecB2

/-! Arithmetic lemmas for arm64 `SDiv`/`SMod`: the `subs`/`sbcs` negation chain and signed-division case splits. -/

open Janus Janus.Arm64

namespace Fv256.Arm64.SDivLemmas

theorem neg4a (a0 a1 a2 a3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) :
    (18446744073709551616 - a0) % 18446744073709551616 +
        18446744073709551616 *
          (((~~~BitVec.ofNat 64 a1).toNat + (addSub (0#64) (BitVec.ofNat 64 a0) true).snd.c.toNat) %
            18446744073709551616) +
      340282366920938463463374607431768211456 *
        (((~~~BitVec.ofNat 64 a2).toNat +
            ((~~~BitVec.ofNat 64 a1).toNat + (addSub (0#64) (BitVec.ofNat 64 a0) true).snd.c.toNat) /
              18446744073709551616) %
          18446744073709551616) +
    6277101735386680763835789423207666416102355444464034512896 *
      (((~~~BitVec.ofNat 64 a3).toNat +
          ((~~~BitVec.ofNat 64 a2).toNat +
              ((~~~BitVec.ofNat 64 a1).toNat + (addSub (0#64) (BitVec.ofNat 64 a0) true).snd.c.toNat) /
                18446744073709551616) /
            18446744073709551616) %
        18446744073709551616) =
    Fv256.Spec.neg (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
      6277101735386680763835789423207666416102355444464034512896 * a3) := by
  simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Fv256.Spec.neg, Fv256.Spec.W, Nat.reducePow]
  by_cases h : a0 = 0 <;> simp [h] <;> omega

theorem sd_pp (X Y : Nat) (hx : X < 2 ^ 255) (hy : Y < 2 ^ 255) :
    Fv256.B.sdivSpec X Y = Fv256.B.divSpec X Y := by
  unfold Fv256.B.sdivSpec Fv256.Spec.abs
  rw [if_pos (by omega), if_pos hx, if_pos hy]

theorem sd_np (X Y : Nat) (hx : 2 ^ 255 ≤ X) (hy : Y < 2 ^ 255) :
    Fv256.B.sdivSpec X Y = Fv256.Spec.neg (Fv256.B.divSpec (Fv256.Spec.neg X) Y) := by
  unfold Fv256.B.sdivSpec Fv256.Spec.abs
  rw [if_neg (by omega), if_neg (by omega), if_pos hy]
  rfl

theorem sd_pn (X Y : Nat) (hx : X < 2 ^ 255) (hy : 2 ^ 255 ≤ Y) :
    Fv256.B.sdivSpec X Y = Fv256.Spec.neg (Fv256.B.divSpec X (Fv256.Spec.neg Y)) := by
  unfold Fv256.B.sdivSpec Fv256.Spec.abs
  rw [if_neg (by omega), if_pos hx, if_neg (by omega)]
  rfl

theorem sd_nn (X Y : Nat) (hx : 2 ^ 255 ≤ X) (hy : 2 ^ 255 ≤ Y) :
    Fv256.B.sdivSpec X Y = Fv256.B.divSpec (Fv256.Spec.neg X) (Fv256.Spec.neg Y) := by
  unfold Fv256.B.sdivSpec Fv256.Spec.abs
  rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

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

end Fv256.Arm64.SDivLemmas
