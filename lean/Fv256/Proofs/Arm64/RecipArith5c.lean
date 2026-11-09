import Fv256.Proofs.Arm64.RecipG.C_698_77c
import Fv256.Proofs.Arm64.RecipArith5
import Fv256.Proofs.Amd64.RecipShr

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
open Fv256.F Fv256.RecipMath

theorem toInt_neg (m : Nat) (h : m < 2 ^ 64) : (BitVec.ofNat 64 m).toInt < 0 ↔ 2 ^ 63 ≤ m := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  split <;> omega

theorem toInt_nonneg (m : Nat) (h : m < 2 ^ 64) : 0 ≤ (BitVec.ofNat 64 m).toInt ↔ m < 2 ^ 63 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  split <;> omega

theorem toInt_pos (m : Nat) (h : m < 2 ^ 64) : 0 < (BitVec.ofNat 64 m).toInt ↔ 0 < m ∧ m < 2 ^ 63 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  split <;> omega

/-- the five-word right shift of the epilogue (arm64 instruction forms) -/
theorem shr_arm (n a0 a1 a2 a3 a4 x0 x1 x2 x3 x4 : Nat) (hn : n < 64)
    (b0 : a0 < 2 ^ 64) (b1 : a1 < 2 ^ 64) (b2 : a2 < 2 ^ 64) (b3 : a3 < 2 ^ 64) (b4 : a4 < 2 ^ 64)
    (h0 : x0 = (if 0 < (BitVec.ofNat 64 n).toInt then ((if (18446744073709551616 - n + 64) % 18446744073709551616 < 64 then a1 * 2 ^ ((18446744073709551616 - n - 18446744073709551552) % 64) % 18446744073709551616 else 0) ||| (BitVec.ofNat 64 a0 >>> (n % 64)).toNat) % 18446744073709551616 else a0)) (h1 : x1 = (if 0 < (BitVec.ofNat 64 n).toInt then ((if (18446744073709551616 - n + 64) % 18446744073709551616 < 64 then a2 * 2 ^ ((18446744073709551616 - n - 18446744073709551552) % 64) % 18446744073709551616 else 0) ||| (BitVec.ofNat 64 a1 >>> (n % 64)).toNat) % 18446744073709551616 else a1)) (h2 : x2 = (if 0 < (BitVec.ofNat 64 n).toInt then ((BitVec.ofNat 64 a2 >>> (n % 64)).toNat ||| if (18446744073709551616 - n + 64) % 18446744073709551616 < 64 then a3 * 2 ^ ((18446744073709551616 - n - 18446744073709551552) % 64) % 18446744073709551616 else 0) % 18446744073709551616 else a2)) (h3 : x3 = (if 0 < (BitVec.ofNat 64 n).toInt then ((BitVec.ofNat 64 a3 >>> (n % 64)).toNat ||| if (18446744073709551616 - n + 64) % 18446744073709551616 < 64 then a4 * 2 ^ ((18446744073709551616 - n - 18446744073709551552) % 64) % 18446744073709551616 else 0) % 18446744073709551616 else a3)) (h4 : x4 = (if 0 < (BitVec.ofNat 64 n).toInt then (BitVec.ofNat 64 a4 >>> (n % 64)).toNat else a4)) :
    x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 = (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4) / 2 ^ n := by
  rcases Nat.eq_zero_or_pos n with hz | hpos
  · subst hz
    have e0 : ¬ (0 < (BitVec.ofNat 64 0).toInt) := by
      rw [toInt_pos 0 (by decide)]; omega
    simp only [e0, if_false] at h0 h1 h2 h3 h4
    rw [h0, h1, h2, h3, h4]; simp
  · have e0 : 0 < (BitVec.ofNat 64 n).toInt := by
      rw [toInt_pos n (by omega)]; omega
    simp only [e0, if_true] at h0 h1 h2 h3 h4
    have ea : (18446744073709551616 - n + 64) % 18446744073709551616 = 64 - n := by omega
    have eb : (18446744073709551616 - n - 18446744073709551552) % 64 = 64 - n := by omega
    have ec : 64 - n < 64 := by omega
    have ed : n % 64 = n := Nat.mod_eq_of_lt hn
    simp only [ea, eb, ed, ec, if_true] at h0 h1 h2 h3 h4
    have sh : ∀ a : Nat, a < 2 ^ 64 → (BitVec.ofNat 64 a >>> n).toNat = a >>> n := fun a ha => Fv256.Amd64.RecipSeg.tw4 a n ha
    have ml : ∀ b : Nat, b * 2 ^ (64 - n) % 18446744073709551616 = (b <<< (64 - n)) % 2 ^ 64 := fun b => by rw [Nat.shiftLeft_eq]
    rw [sh a0 b0, ml] at h0
    rw [sh a1 b1, ml] at h1
    rw [sh a2 b2, ml] at h2
    rw [sh a3 b3, ml] at h3
    rw [sh a4 b4] at h4
    have s5 := Fv256.Amd64.RecipSeg.shr5 n a0 a1 a2 a3 a4 hpos hn b0 b1 b2 b3 b4
    have l0 := Fv256.Amd64.RecipSeg.tw_lt a0 a1 n b0
    have l1 := Fv256.Amd64.RecipSeg.tw_lt a1 a2 n b1
    have l2 := Fv256.Amd64.RecipSeg.tw_lt a2 a3 n b2
    have l3 := Fv256.Amd64.RecipSeg.tw_lt a3 a4 n b3
    rw [Nat.or_comm ((a1 <<< (64 - n)) % 2 ^ 64)] at h0
    rw [Nat.or_comm ((a2 <<< (64 - n)) % 2 ^ 64)] at h1
    rw [← s5, h0, h1, h2, h3, h4, Nat.mod_eq_of_lt l0, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2, Nat.mod_eq_of_lt l3]

theorem sum5c (x698r0 x698r1 x698r4 x698m80 x698m88 x698m96 x698m176 : Nat) (x708r0 x708r1 x708r2 x708r3 x708r4 x708r5 x77cm280 x77cm288 x77cm296 x77cm304 x77cm312 : Nat)
    (b1 : x698r1 < 2 ^ 64) (b96 : x698m96 < 2 ^ 64) (b88 : x698m88 < 2 ^ 64) (b4 : x698r4 < 2 ^ 64) (b80 : x698m80 < 2 ^ 64)
    (hf : x698r0 ≤ 1) (hm : x698m176 < 2 ^ 64) (hs : x698m176 < 64 ∨ 2 ^ 63 ≤ x698m176)
    (h_x708r0 : x708r0 = (if (BitVec.ofNat 64 x698m176).toInt < 0 then ((if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) + if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) % 18446744073709551616 else if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616)) (h_x708r1 : x708r1 = (if (BitVec.ofNat 64 x698m176).toInt < 0 then (((if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + ((if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) + if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616)) (h_x708r2 : x708r2 = (if (BitVec.ofNat 64 x698m176).toInt < 0 then (((if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616) + if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616) + (((if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + ((if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) + if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616)) (h_x708r3 : x708r3 = (if (BitVec.ofNat 64 x698m176).toInt < 0 then (((if x698r0 = 0 then x698r4 else (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + if x698r0 = 0 then x698r4 else (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (((if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616) + if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616) + (((if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + ((if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) + if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else if x698r0 = 0 then x698r4 else (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)) (h_x708r4 : x708r4 = (if (BitVec.ofNat 64 x698m176).toInt < 0 then (((if x698r0 = 0 then x698m80 else (x698m80 + (18446744073709551616 - 1 - 0) + (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + if x698r0 = 0 then x698m80 else (x698m80 + (18446744073709551616 - 1 - 0) + (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (((if x698r0 = 0 then x698r4 else (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + if x698r0 = 0 then x698r4 else (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (((if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616) + if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616) + (((if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) + ((if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) + if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else if x698r0 = 0 then x698m80 else (x698m80 + (18446744073709551616 - 1 - 0) + (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)) (h_x708r5 : x708r5 = (if 0 ≤ (BitVec.ofNat 64 x698m176).toInt then x698m176 else 0)) (h_x77cm280 : x77cm280 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then ((if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then x708r1 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64) % 18446744073709551616 else 0) ||| (BitVec.ofNat 64 x708r0 >>> (x708r5 % 64)).toNat) % 18446744073709551616 else x708r0)) (h_x77cm288 : x77cm288 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then ((if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then x708r2 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64) % 18446744073709551616 else 0) ||| (BitVec.ofNat 64 x708r1 >>> (x708r5 % 64)).toNat) % 18446744073709551616 else x708r1)) (h_x77cm296 : x77cm296 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then ((BitVec.ofNat 64 x708r2 >>> (x708r5 % 64)).toNat ||| if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then x708r3 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64) % 18446744073709551616 else 0) % 18446744073709551616 else x708r2)) (h_x77cm304 : x77cm304 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then ((BitVec.ofNat 64 x708r3 >>> (x708r5 % 64)).toNat ||| if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then x708r4 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64) % 18446744073709551616 else 0) % 18446744073709551616 else x708r3)) (h_x77cm312 : x77cm312 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then (BitVec.ofNat 64 x708r4 >>> (x708r5 % 64)).toNat else x708r4))
    : x77cm280 + 2 ^ 64 * x77cm288 + 2 ^ 128 * x77cm296 + 2 ^ 192 * x77cm304 + 2 ^ 256 * x77cm312 =
      (if 2 ^ 63 ≤ x698m176 then 2 * (if x698r0 = 0 then (x698r1 + 2 ^ 64 * x698m96 + 2 ^ 128 * x698m88 + 2 ^ 192 * x698r4 + 2 ^ 256 * x698m80) else ((x698r1 + 2 ^ 64 * x698m96 + 2 ^ 128 * x698m88 + 2 ^ 192 * x698r4 + 2 ^ 256 * x698m80) + 2 ^ 320 - 1) % 2 ^ 320) % 2 ^ 320 else (if x698r0 = 0 then (x698r1 + 2 ^ 64 * x698m96 + 2 ^ 128 * x698m88 + 2 ^ 192 * x698r4 + 2 ^ 256 * x698m80) else ((x698r1 + 2 ^ 64 * x698m96 + 2 ^ 128 * x698m88 + 2 ^ 192 * x698r4 + 2 ^ 256 * x698m80) + 2 ^ 320 - 1) % 2 ^ 320) / 2 ^ x698m176) := by
  have hneg := toInt_neg x698m176 hm
  have hnn := toInt_nonneg x698m176 hm
  generalize hd4 : (if x698r0 = 0 then x698m80 else (x698m80 + (18446744073709551616 - 1 - 0) + (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) = D4 at h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4
  generalize hd3 : (if x698r0 = 0 then x698r4 else (x698r4 + (18446744073709551616 - 1 - 0) + (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) = D3 at h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4
  generalize hd2 : (if x698r0 = 0 then x698m88 else (x698m88 + (18446744073709551616 - 1 - 0) + (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) / 18446744073709551616) % 18446744073709551616) = D2 at h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4
  generalize hd1 : (if x698r0 = 0 then x698m96 else (x698m96 + (18446744073709551616 - 1 - 0) + (decide (1 ≤ x698r1)).toNat) % 18446744073709551616) = D1 at h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4
  generalize hd0 : (if x698r0 = 0 then x698r1 else (18446744073709551616 - 1 + x698r1) % 18446744073709551616) = D0 at h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4
  have hD : D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3 + 2 ^ 256 * D4 = (if x698r0 = 0 then (x698r1 + 2 ^ 64 * x698m96 + 2 ^ 128 * x698m88 + 2 ^ 192 * x698r4 + 2 ^ 256 * x698m80) else ((x698r1 + 2 ^ 64 * x698m96 + 2 ^ 128 * x698m88 + 2 ^ 192 * x698r4 + 2 ^ 256 * x698m80) + 2 ^ 320 - 1) % 2 ^ 320) := by
    rw [← hd0, ← hd1, ← hd2, ← hd3, ← hd4]
    by_cases hz : x698r0 = 0
    · simp only [hz, if_true]
    · simp only [hz, if_false]
      simp (disch := first | decide | omega) only [Fv256.AM.dec_le_div]
      janus_carry
  have bD : D0 < 2 ^ 64 ∧ D1 < 2 ^ 64 ∧ D2 < 2 ^ 64 ∧ D3 < 2 ^ 64 ∧ D4 < 2 ^ 64 := by
    rw [← hd0, ← hd1, ← hd2, ← hd3, ← hd4]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> split <;> first | assumption | exact Nat.mod_lt _ (by decide)
  obtain ⟨bD0, bD1, bD2, bD3, bD4⟩ := bD
  by_cases hN : 2 ^ 63 ≤ x698m176
  · have ht : (BitVec.ofNat 64 x698m176).toInt < 0 := hneg.2 hN
    have hnt : ¬ (0 ≤ (BitVec.ofNat 64 x698m176).toInt) := fun h => by have := hnn.1 h; omega
    simp only [ht, if_true] at h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4
    have h5 : x708r5 = 0 := by rw [h_x708r5]; simp only [hnt, if_false]
    have e0 : ¬ (0 < (BitVec.ofNat 64 x708r5).toInt) := by
      rw [h5, toInt_pos 0 (by decide)]; omega
    simp only [e0, if_false] at h_x77cm280 h_x77cm288 h_x77cm296 h_x77cm304 h_x77cm312
    rw [if_pos hN, ← hD, h_x77cm280, h_x77cm288, h_x77cm296, h_x77cm304, h_x77cm312, h_x708r0, h_x708r1, h_x708r2, h_x708r3, h_x708r4]
    janus_carry
  · have ht : ¬ (BitVec.ofNat 64 x698m176).toInt < 0 := fun h => hN (hneg.1 h)
    have hnt : 0 ≤ (BitVec.ofNat 64 x698m176).toInt := hnn.2 (by omega)
    simp only [ht, if_false] at h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4
    have h5 : x708r5 = x698m176 := by rw [h_x708r5]; simp only [hnt, if_true]
    have hn64 : x698m176 < 64 := by omega
    rw [if_neg hN, ← hD]
    have := shr_arm x708r5 x708r0 x708r1 x708r2 x708r3 x708r4 x77cm280 x77cm288 x77cm296 x77cm304 x77cm312 (by omega) (by rw [h_x708r0]; assumption) (by rw [h_x708r1]; assumption) (by rw [h_x708r2]; assumption) (by rw [h_x708r3]; assumption) (by rw [h_x708r4]; assumption) h_x77cm280 h_x77cm288 h_x77cm296 h_x77cm304 h_x77cm312
    rw [this, h_x708r0, h_x708r1, h_x708r2, h_x708r3, h_x708r4, h5]

end Fv256.Arm64.RecipSeg
