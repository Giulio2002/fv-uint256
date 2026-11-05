import Janus
import Fv256.Spec
import Fv256.Util
import Fv256.UtilB
import Fv256.Arm64.KnuthLem

open Janus Janus.Arm64
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.DivMLem
open Fv256.Arm64.KnuthLem

theorem awc_fst_neg (x y : BitVec 64) (c : Bool) :
    (addWithCarry x (~~~y) c).fst.toNat = (x.toNat + (2 ^ 64 - 1 - y.toNat) + c.toNat) % 2 ^ 64 := by
  rw [awc_fst, BitVec.toNat_not]

theorem awc_c_neg (x y : BitVec 64) (c : Bool) :
    (addWithCarry x (~~~y) c).snd.c = decide (2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + c.toNat) := by
  rw [awc_c, BitVec.toNat_not]

/-- The no-borrow test of `x - y` over four limbs, in the shape the machine code leaves (`NGC`, `NEG` chain). -/
theorem nb4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64) (h3 : a3 < 2 ^ 64)
    (g0 : b0 < 2 ^ 64) (g1 : b1 < 2 ^ 64) (g2 : b2 < 2 ^ 64) (g3 : b3 < 2 ^ 64) :
    (2 ^ 64 - (addWithCarry (0#64) (18446744073709551615#64)
        (addWithCarry (BitVec.ofNat 64 a3) (~~~BitVec.ofNat 64 b3)
          (addWithCarry (BitVec.ofNat 64 a2) (~~~BitVec.ofNat 64 b2)
            (addWithCarry (BitVec.ofNat 64 a1) (~~~BitVec.ofNat 64 b1) (decide (b0 ≤ a0))).snd.c).snd.c).snd.c).fst.toNat) % 2 ^ 64 = 0 ↔
    b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3 ≤ a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 := by
  rw [awc_fst, awc_c_neg, awc_c_neg, awc_c_neg]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3,
    Nat.mod_eq_of_lt g1, Nat.mod_eq_of_lt g2, Nat.mod_eq_of_lt g3]
  generalize hk0 : decide (b0 ≤ a0) = k0
  cases k0 <;> simp only [decide_eq_false_iff_not, decide_eq_true_eq, Bool.toNat_true, Bool.toNat_false] at hk0 <;>
  generalize hk1 : decide (2 ^ 64 ≤ a1 + (2 ^ 64 - 1 - b1) + _) = k1 <;>
  cases k1 <;> simp only [decide_eq_false_iff_not, decide_eq_true_eq, Bool.toNat_true, Bool.toNat_false] at hk1 <;>
  generalize hk2 : decide (2 ^ 64 ≤ a2 + (2 ^ 64 - 1 - b2) + _) = k2 <;>
  cases k2 <;> simp only [decide_eq_false_iff_not, decide_eq_true_eq, Bool.toNat_true, Bool.toNat_false] at hk2 <;>
  generalize hk3 : decide (2 ^ 64 ≤ a3 + (2 ^ 64 - 1 - b3) + _) = k3 <;>
  cases k3 <;> simp only [decide_eq_false_iff_not, decide_eq_true_eq, Bool.toNat_true, Bool.toNat_false] at hk3 ⊢ <;> simp only [Nat.reducePow, true_iff, iff_true, false_iff, iff_false] at * <;> omega

end Fv256.Arm64.DivMLem
