import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

/-!
# arm64 `udivremBy1`: the Möller-Granlund 2-by-1 step as the compiled code performs it

`step_rem` / `step_quot` identify the machine's remainder and quotient expressions (with `X` the high word
`qh` of the estimate) with `Fv256.B.div2by1`; `qh_val` evaluates `qh`.
-/

open Janus Janus.Arm64

namespace Fv256.Arm64.By1Math

theorem qh_val (v rem uk : Nat) (hv : v < 2 ^ 64) (hrem : rem < 2 ^ 64) (huk : uk < 2 ^ 64) :
    ((addWithCarry (BitVec.ofNat 64 rem)
        (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 v) * BitVec.setWidth 128 (BitVec.ofNat 64 rem)))
        (addWithCarry (BitVec.ofNat 64 v * BitVec.ofNat 64 rem) (BitVec.ofNat 64 uk) false).snd.c).fst).toNat =
      ((v * rem) / 2 ^ 64 + rem + ((v * rem) % 2 ^ 64 + uk) / 2 ^ 64) % 2 ^ 64 := by
  have hVR : (BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat = (v * rem) % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hrem]
  have hU : (BitVec.ofNat 64 uk).toNat = uk := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt huk
  have hc : (addWithCarry (BitVec.ofNat 64 v * BitVec.ofNat 64 rem) (BitVec.ofNat 64 uk) false).snd.c =
      decide (2 ^ 64 ≤ (v * rem) % 2 ^ 64 + uk) := by
    simp only [addWithCarry, Bool.toNat_false, hVR, hU, BitVec.toNat_ofNat]
    generalize v * rem % 2 ^ 64 = X at *
    apply decide_eq_decide.mpr
    omega
  have hhi : (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 v) * BitVec.setWidth 128 (BitVec.ofNat 64 rem))).toNat =
      (v * rem) / 2 ^ 64 := by
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [Nat.shiftRight_eq_div_pow]
    have hp : v * rem < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hv hrem
    rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hrem, Nat.mod_eq_of_lt (by omega : v < 2 ^ 128), Nat.mod_eq_of_lt (by omega : rem < 2 ^ 128),
      Nat.mod_eq_of_lt (by have : 2 ^ 64 * 2 ^ 64 = 2 ^ 128 := by rw [← Nat.pow_add]
                           omega : v * rem < 2 ^ 128)]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hp)
  have key : ∀ (x y : BitVec 64) (c : Bool), (addWithCarry x y c).fst.toNat = (x.toNat + y.toNat + c.toNat) % 2 ^ 64 := by
    intro x y c; simp [addWithCarry]
  rw [key, hhi, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem]
  by_cases hP : 2 ^ 64 ≤ (v * rem) % 2 ^ 64 + uk
  · have : ((v * rem) % 2 ^ 64 + uk) / 2 ^ 64 = 1 := by omega
    simp only [hP, decide_true, Bool.toNat_true, this]; omega
  · have : ((v * rem) % 2 ^ 64 + uk) / 2 ^ 64 = 0 := by omega
    simp only [hP, decide_false, Bool.toNat_false, this]; omega

set_option maxHeartbeats 8000000 in
theorem step_rem (v rem uk d : Nat) (X : BitVec 64) (hv : v < 2 ^ 64) (hrem : rem < 2 ^ 64) (huk : uk < 2 ^ 64)
    (hd : d < 2 ^ 64)
    (hX : X.toNat = ((v * rem) / 2 ^ 64 + rem + ((v * rem) % 2 ^ 64 + uk) / 2 ^ 64) % 2 ^ 64) :
    (if d ≤ (if ((BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat + uk) % 18446744073709551616 <
            (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616 then
          BitVec.ofNat 64 d + (BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64))
        else BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64)).toNat then
      (if ((BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat + uk) % 18446744073709551616 <
            (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616 then
          BitVec.ofNat 64 d + (BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64))
        else BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64)) - BitVec.ofNat 64 d
    else
      if ((BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat + uk) % 18446744073709551616 <
            (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616 then
          BitVec.ofNat 64 d + (BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64))
        else BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64)) =
      BitVec.ofNat 64 (Fv256.B.div2by1 (2 ^ 64) d v rem uk).2 := by
  apply BitVec.eq_of_toNat_eq
  unfold Fv256.B.div2by1
  dsimp only
  have hVR : (BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat = (v * rem) % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hrem]
  have hX1 : (X + 1#64).toNat = (X.toNat + 1) % 2 ^ 64 := by
    rw [BitVec.toNat_add]; simp
  have hDQ : (BitVec.ofNat 64 d * (X + 1#64)).toNat = (d * ((X.toNat + 1) % 2 ^ 64)) % 2 ^ 64 := by
    rw [BitVec.toNat_mul, hX1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hDQ' : (BitVec.ofNat 64 d * (X + 1#64)).toNat = d * ((X.toNat + 1) % 2 ^ 64) % 2 ^ 64 := hDQ
  have hXlt : X.toNat < 2 ^ 64 := X.isLt
  generalize hP : v * rem = P at *
  have hPB : P < 2 ^ 64 * 2 ^ 64 := hP ▸ Nat.mul_lt_mul'' hv hrem
  have hPB2 : P / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
  have hUk : (BitVec.ofNat 64 uk).toNat = uk := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt huk
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hd
  by_cases hc : (P % 2 ^ 64 + uk) % 18446744073709551616 <
      (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616
  · simp only [hVR, hc, ite_true]
    rw [apply_ite BitVec.toNat]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, hUk, hD, hDQ', BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
    rw [hX] at hX1 hDQ'
    simp only [Nat.reducePow, hX] 
    simp only [Nat.reducePow] at hX1 hDQ' hXlt
    generalize hQ : ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + uk) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 = Q at *
    have hQl : Q < 18446744073709551616 := by omega
    have hm := Nat.mul_comm d Q
    repeat' split
    all_goals omega
  · simp only [hVR, hc, ite_false]
    rw [apply_ite BitVec.toNat]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, hUk, hD, hDQ', BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
    rw [hX] at hX1 hDQ'
    simp only [Nat.reducePow, hX] 
    simp only [Nat.reducePow] at hX1 hDQ' hXlt
    generalize hQ : ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + uk) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 = Q at *
    have hQl : Q < 18446744073709551616 := by omega
    have hm := Nat.mul_comm d Q
    repeat' split
    all_goals omega


set_option maxHeartbeats 8000000 in
theorem step_quot (v rem uk d : Nat) (X : BitVec 64) (hv : v < 2 ^ 64) (hrem : rem < 2 ^ 64) (huk : uk < 2 ^ 64)
    (hd : d < 2 ^ 64)
    (hX : X.toNat = ((v * rem) / 2 ^ 64 + rem + ((v * rem) % 2 ^ 64 + uk) / 2 ^ 64) % 2 ^ 64) :
    (if (if ((BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat + uk) % 18446744073709551616 <
            (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616 then
          BitVec.ofNat 64 d + (BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64))
        else BitVec.ofNat 64 uk - BitVec.ofNat 64 d * (X + 1#64)).toNat < d then
        (if ((BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat + uk) % 18446744073709551616 <
            (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616 then X else X + 1#64)
      else (if ((BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat + uk) % 18446744073709551616 <
            (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616 then X else X + 1#64) + 1#64).toNat % 2 ^ 64 =
      (Fv256.B.div2by1 (2 ^ 64) d v rem uk).1 % 2 ^ 64 := by
  unfold Fv256.B.div2by1
  dsimp only
  have hVR : (BitVec.ofNat 64 v * BitVec.ofNat 64 rem).toNat = (v * rem) % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hrem]
  have hX1 : (X + 1#64).toNat = (X.toNat + 1) % 2 ^ 64 := by
    rw [BitVec.toNat_add]; simp
  have hDQ : (BitVec.ofNat 64 d * (X + 1#64)).toNat = (d * ((X.toNat + 1) % 2 ^ 64)) % 2 ^ 64 := by
    rw [BitVec.toNat_mul, hX1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hDQ' : (BitVec.ofNat 64 d * (X + 1#64)).toNat = d * ((X.toNat + 1) % 2 ^ 64) % 2 ^ 64 := hDQ
  have hXlt : X.toNat < 2 ^ 64 := X.isLt
  generalize hP : v * rem = P at *
  have hPB : P < 2 ^ 64 * 2 ^ 64 := hP ▸ Nat.mul_lt_mul'' hv hrem
  have hPB2 : P / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
  have hUk : (BitVec.ofNat 64 uk).toNat = uk := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt huk
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hd
  by_cases hc : (P % 2 ^ 64 + uk) % 18446744073709551616 <
      (18446744073709551616 - (BitVec.ofNat 64 d * (X + 1#64)).toNat + uk) % 18446744073709551616
  · simp only [hVR, hc, ite_true]
    simp only [apply_ite BitVec.toNat]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, hUk, hD, hDQ', BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
    rw [hX] at hX1 hDQ'
    simp only [Nat.reducePow, hX] 
    simp only [Nat.reducePow] at hX1 hDQ' hXlt
    generalize hQ : ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + uk) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 = Q at *
    have hQl : Q < 18446744073709551616 := by omega
    have hm := Nat.mul_comm d Q
    repeat' split
    all_goals omega
  · simp only [hVR, hc, ite_false]
    simp only [apply_ite BitVec.toNat]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, hUk, hD, hDQ', BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
    rw [hX] at hX1 hDQ'
    simp only [Nat.reducePow, hX] 
    simp only [Nat.reducePow] at hX1 hDQ' hXlt
    generalize hQ : ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + uk) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 = Q at *
    have hQl : Q < 18446744073709551616 := by omega
    have hm := Nat.mul_comm d Q
    repeat' split
    all_goals omega


end Fv256.Arm64.By1Math
