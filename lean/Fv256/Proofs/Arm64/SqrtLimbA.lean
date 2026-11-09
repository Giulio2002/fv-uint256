import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.UtilD
import Fv256.Proofs.Arm64.ExpLoopLem

open Janus Janus.Arm64

namespace Fv256.Arm64.SqrtLimbA

theorem extr1 (hi lo : BitVec 64) :
    (BitVec.extractLsb' 1 64 (hi ++ lo)).toNat = lo.toNat / 2 + (hi.toNat % 2) * 2 ^ 63 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append]
  have hl := lo.isLt
  have hh := hi.isLt
  rw [Nat.shiftLeft_eq, Nat.or_comm, Fv256.D.or_add _ _ _ hl, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  omega

theorem rot_top (v : BitVec 64) : ((v.rotateRight 1).toNat % 9223372036854775808) = v.toNat / 2 := by
  have h := Fv256.Arm64.ExpLoopLem.lsr1_gen v
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h2
  have hr := (v.rotateRight 1).isLt
  have e1 : (v.rotateRight 1).toNat &&& (18446744073709551615#64).toNat = (v.rotateRight 1).toNat := by
    simp only [BitVec.toNat_ofNat]
    rw [show (18446744073709551615 % 2 ^ 64 : Nat) = 2 ^ 64 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hr]
  rw [e1] at h2
  simp only [BitVec.toNat_ofNat] at h2
  rw [show (9223372036854775807 % 2 ^ 64 : Nat) = 2 ^ 63 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at h2
  simpa using h2

theorem awc_fst (x y : Nat) (c : Bool) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (addWithCarry (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) c).fst.toNat = (x + y + c.toNat) % 2 ^ 64 := by
  simp only [addWithCarry, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem awc_c (x y : Nat) (c : Bool) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (addWithCarry (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) c).snd.c.toNat = (x + y + c.toNat) / 2 ^ 64 := by
  simp only [addWithCarry, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  have hc := Bool.toNat_le c
  by_cases h : (x + y + c.toNat) % 2 ^ 64 = x + y + c.toNat
  · simp [h]; omega
  · simp [h]; omega

/-- the add-and-shift of the 256-bit Newton loop body, in the form the arm64 executor produces -/
theorem add_shr_arm (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (hb3 : b3 < 2 ^ 64)
    (hlt : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) < 2 ^ 256) :
    (BitVec.extractLsb' 1 64 ((addWithCarry (BitVec.ofNat 64 a1) (BitVec.ofNat 64 b1) (addWithCarry (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) false).snd.c).fst ++ ((BitVec.ofNat 64 a0) + (BitVec.ofNat 64 b0)))).toNat + 2 ^ 64 * (BitVec.extractLsb' 1 64 ((addWithCarry (BitVec.ofNat 64 a2) (BitVec.ofNat 64 b2) (addWithCarry (BitVec.ofNat 64 a1) (BitVec.ofNat 64 b1) (addWithCarry (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) false).snd.c).snd.c).fst ++ (addWithCarry (BitVec.ofNat 64 a1) (BitVec.ofNat 64 b1) (addWithCarry (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) false).snd.c).fst)).toNat + 2 ^ 128 * (BitVec.extractLsb' 1 64 ((addWithCarry (BitVec.ofNat 64 a3) (BitVec.ofNat 64 b3) (addWithCarry (BitVec.ofNat 64 a2) (BitVec.ofNat 64 b2) (addWithCarry (BitVec.ofNat 64 a1) (BitVec.ofNat 64 b1) (addWithCarry (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) false).snd.c).snd.c).snd.c).fst ++ (addWithCarry (BitVec.ofNat 64 a2) (BitVec.ofNat 64 b2) (addWithCarry (BitVec.ofNat 64 a1) (BitVec.ofNat 64 b1) (addWithCarry (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) false).snd.c).snd.c).fst)).toNat + 2 ^ 192 * (((addWithCarry (BitVec.ofNat 64 a3) (BitVec.ofNat 64 b3) (addWithCarry (BitVec.ofNat 64 a2) (BitVec.ofNat 64 b2) (addWithCarry (BitVec.ofNat 64 a1) (BitVec.ofNat 64 b1) (addWithCarry (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) false).snd.c).snd.c).snd.c).fst.rotateRight 1).toNat % 9223372036854775808) = ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
  have e0 : (BitVec.ofNat 64 a0 + BitVec.ofNat 64 b0).toNat = (a0 + b0) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt hb0]
  have k0 : (addWithCarry (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) false).snd.c.toNat = (a0 + b0) / 2 ^ 64 := by
    rw [awc_c _ _ _ ha0 hb0]; simp
  simp only [extr1, rot_top, awc_fst, awc_c, e0, k0, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
  omega

theorem awc_fst' (x y : BitVec 64) (c : Bool) : (addWithCarry x y c).fst.toNat = (x.toNat + y.toNat + c.toNat) % 2 ^ 64 := by
  simp only [addWithCarry, BitVec.toNat_ofNat]

theorem awc_c' (x y : BitVec 64) (c : Bool) : (addWithCarry x y c).snd.c.toNat = (x.toNat + y.toNat + c.toNat) / 2 ^ 64 := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [addWithCarry, BitVec.toNat_ofNat]
  have hc := Bool.toNat_le c
  by_cases h : (x.toNat + y.toNat + c.toNat) % 2 ^ 64 = x.toNat + y.toNat + c.toNat
  · simp [h]; omega
  · simp [h]; omega

theorem notv (a : Nat) (ha : a < 2 ^ 64) : (~~~BitVec.ofNat 64 a).toNat = 2 ^ 64 - 1 - a := by
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-- the comparison `new z2 >= z1` of the Newton loop: the borrow chain of the subtraction -/
theorem cmp_arm (T0 T1 T2 T3 : BitVec 64) (a0 a1 a2 a3 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64)
    (ha3 : a3 < 2 ^ 64) :
    (18446744073709551616 -
        (addWithCarry (0#64) (18446744073709551615#64)
          (addWithCarry T3 (~~~BitVec.ofNat 64 a3)
            (addWithCarry T2 (~~~BitVec.ofNat 64 a2)
              (addWithCarry T1 (~~~BitVec.ofNat 64 a1)
                (addSub T0 (BitVec.ofNat 64 a0) true).snd.c).snd.c).snd.c).snd.c).fst.toNat) % 18446744073709551616 = 0 ↔
      a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 ≤ T0.toNat + 2 ^ 64 * T1.toNat + 2 ^ 128 * T2.toNat + 2 ^ 192 * T3.toNat := by
  have h0 : (addSub T0 (BitVec.ofNat 64 a0) true) = addWithCarry T0 (~~~BitVec.ofNat 64 a0) true := rfl
  rw [h0]
  have t0 := T0.isLt
  have t1 := T1.isLt
  have t2 := T2.isLt
  have t3 := T3.isLt
  simp only [awc_fst', awc_c', notv _ ha0, notv _ ha1, notv _ ha2, notv _ ha3, BitVec.toNat_ofNat, Bool.toNat_true]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.zero_add]
  omega

theorem t3_eq (v : BitVec 64) :
    (v.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64).toNat = (v.rotateRight 1).toNat % 9223372036854775808 := by
  rw [Fv256.Arm64.ExpLoopLem.lsr1_gen]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := rot_top v
  omega

end Fv256.Arm64.SqrtLimbA
