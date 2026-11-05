import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

open Janus Janus.Arm64 Janus.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthLem

theorem awc_fst (x y : BitVec 64) (c : Bool) : (addWithCarry x y c).fst.toNat = (x.toNat + y.toNat + c.toNat) % 2 ^ 64 := by
  simp [addWithCarry]
theorem awc_c (x y : BitVec 64) (c : Bool) : (addWithCarry x y c).snd.c = decide (2 ^ 64 ≤ x.toNat + y.toNat + c.toNat) := by
  have := x.isLt; have := y.isLt
  simp only [addWithCarry, BitVec.toNat_ofNat]
  have hb := Bool.toNat_le c
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat + c.toNat
  · have : (x.toNat + y.toNat + c.toNat) % 2 ^ 64 ≠ x.toNat + y.toNat + c.toNat := by omega
    simp [this, h]
  · rw [Nat.mod_eq_of_lt (by omega)]; simp [h]

theorem addSub_sub_c (x y : BitVec 64) : (addSub x y true).snd.c = decide (y.toNat ≤ x.toNat) := by
  have := x.isLt; have := y.isLt
  simp only [addSub, ite_true, awc_c, BitVec.toNat_not, Bool.toNat_true]
  by_cases h : y.toNat ≤ x.toNat
  · rw [decide_eq_true h, decide_eq_true]; omega
  · rw [decide_eq_false h, decide_eq_false]; omega

theorem ngc_toNat (c : Bool) : (addWithCarry (0#64) (18446744073709551615#64) c).fst.toNat = if c then 0 else 2 ^ 64 - 1 := by
  rw [awc_fst]; cases c <;> simp

theorem submul_borrow (x y b q : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hq : q < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 q) * BitVec.setWidth 128 (BitVec.ofNat 64 y)) -
      ((addWithCarry (0#64) (18446744073709551615#64) (addSub (BitVec.ofNat 64 x) (BitVec.ofNat 64 b) true).snd.c).fst +
        (addWithCarry (0#64) (18446744073709551615#64)
            (addSub (BitVec.ofNat 64 x - BitVec.ofNat 64 b) (BitVec.ofNat 64 q * BitVec.ofNat 64 y) true).snd.c).fst)).toNat =
    q * y / 2 ^ 64 + (decide (x < b)).toNat + (decide ((2 ^ 64 - b + x) % 2 ^ 64 < q * y % 2 ^ 64)).toNat := by
  obtain ⟨h1, h2⟩ := Fv256.B.submul_step x y q b hx hy hq hb
  have hP : q * y < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hq hy
  have hP2 : q * y / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hP
  rw [BitVec.toNat_sub, BitVec.toNat_add, ngc_toNat, ngc_toNat, addSub_sub_c, addSub_sub_c]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub]
  have e1 : x % 2 ^ 64 = x := Nat.mod_eq_of_lt hx
  have e2 : b % 2 ^ 64 = b := Nat.mod_eq_of_lt hb
  have e3 : q % 2 ^ 64 = q := Nat.mod_eq_of_lt hq
  have e4 : y % 2 ^ 64 = y := Nat.mod_eq_of_lt hy
  have e5 : q % 2 ^ 128 = q := Nat.mod_eq_of_lt (by omega)
  have e6 : y % 2 ^ 128 = y := Nat.mod_eq_of_lt (by omega)
  have e7 : q * y % 2 ^ 128 = q * y := Nat.mod_eq_of_lt (by omega)
  simp only [e1, e2, e3, e4, e5, e6, e7, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hP2]
  generalize q * y = P at *
  simp only [decide_eq_true_eq]
  have hm := Nat.mod_lt P (show 0 < 2 ^ 64 by decide)
  rcases Nat.lt_or_ge x b with c1 | c1 <;> rcases Nat.lt_or_ge ((2 ^ 64 - b + x) % 2 ^ 64) (P % 2 ^ 64) with c2 | c2
  · have n1 : ¬ b ≤ x := by omega
    have n2 : ¬ P % 2 ^ 64 ≤ (2 ^ 64 - b + x) % 2 ^ 64 := by omega
    simp only [c1, c2, n1, n2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, if_false]; omega
  · have n1 : ¬ b ≤ x := by omega
    have n2 : P % 2 ^ 64 ≤ (2 ^ 64 - b + x) % 2 ^ 64 := by omega
    have n3 : ¬ ((2 ^ 64 - b + x) % 2 ^ 64 < P % 2 ^ 64) := by omega
    simp only [c1, n3, n1, n2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, if_false, if_true]; omega
  · have n1 : b ≤ x := by omega
    have n2 : ¬ P % 2 ^ 64 ≤ (2 ^ 64 - b + x) % 2 ^ 64 := by omega
    have n3 : ¬ x < b := by omega
    simp only [n3, c2, n1, n2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, if_false, if_true]; omega
  · have n1 : b ≤ x := by omega
    have n2 : P % 2 ^ 64 ≤ (2 ^ 64 - b + x) % 2 ^ 64 := by omega
    have n3 : ¬ x < b := by omega
    have n4 : ¬ ((2 ^ 64 - b + x) % 2 ^ 64 < P % 2 ^ 64) := by omega
    simp only [n3, n4, n1, n2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, if_false, if_true]; omega

theorem qh_val (u2 u1 v : Nat) (h2 : u2 < 2^64) (h1 : u1 < 2^64) (hv : v < 2^64) :
    ((addWithCarry (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 u2) * BitVec.setWidth 128 (BitVec.ofNat 64 v)))
        (BitVec.ofNat 64 u2) (addWithCarry (BitVec.ofNat 64 u2 * BitVec.ofNat 64 v) (BitVec.ofNat 64 u1) false).snd.c).fst).toNat
      = (v * u2 / 2 ^ 64 + u2 + (v * u2 % 2 ^ 64 + u1) / 2 ^ 64) % 2 ^ 64 := by
  rw [awc_fst, awc_c]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]
  have e1 : u2 % 2 ^ 64 = u2 := Nat.mod_eq_of_lt h2
  have e2 : u1 % 2 ^ 64 = u1 := Nat.mod_eq_of_lt h1
  have e3 : v % 2 ^ 64 = v := Nat.mod_eq_of_lt hv
  rw [e1, e2, e3]
  have hP : v * u2 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hv h2
  have e4 : u2 % 2 ^ 128 = u2 := Nat.mod_eq_of_lt (by omega)
  have e5 : v % 2 ^ 128 = v := Nat.mod_eq_of_lt (by omega)
  have e6 : v * u2 % 2 ^ 128 = v * u2 := Nat.mod_eq_of_lt (by omega)
  rw [e4, e5, Nat.mul_comm u2 v, e6, Nat.shiftRight_eq_div_pow]
  have hP2 : v * u2 / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hP
  rw [Nat.mod_eq_of_lt hP2]
  have hm := Nat.mod_lt (v * u2) (show 0 < 2 ^ 64 by decide)
  have hc : (decide (2 ^ 64 ≤ v * u2 % 2 ^ 64 + u1 + false.toNat)).toNat = (v * u2 % 2 ^ 64 + u1) / 2 ^ 64 := by
    have hb : false.toNat = 0 := rfl
    rw [hb, Nat.add_zero]
    by_cases h : 2 ^ 64 ≤ v * u2 % 2 ^ 64 + u1
    · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega
    · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega
  rw [hc]


end Fv256.Arm64.KnuthLem
