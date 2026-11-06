import Fv256.Spec
import Fv256.Util
import Fv256.UtilD

/-! The limb arithmetic of the Newton loop body of `Sqrt` (256-bit path): add `z1` into `z2` with carries and shift right by one. -/

namespace Fv256.SqrtLimb

open Fv256

/-- one shifted limb: `(hi << 63) | (v >> 1)` on 64-bit words, as a number -/
theorem shr_limb (v : BitVec 64) (hi : Nat) :
    ((BitVec.ofNat 64 hi <<< 63) ||| (v >>> 1)).toNat = v.toNat / 2 + (hi % 2) * 2 ^ 63 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h1 : hi % 2 ^ 64 * 2 ^ 63 % 2 ^ 64 = (hi % 2) * 2 ^ 63 := by
    have : hi % 2 ^ 64 % 2 = hi % 2 := Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)
    omega
  rw [h1]
  have h2 : v.toNat / 2 ^ 1 < 2 ^ 63 := by have := v.isLt; omega
  rw [Nat.or_comm, D.or_add _ _ _ h2, Nat.pow_one]

/-- the top limb: `hi >> 1` -/
theorem shr_top (hi : Nat) (h : hi < 2 ^ 64) : (BitVec.ofNat 64 hi >>> 1).toNat = hi / 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow, Nat.pow_one]


/-- the add-and-shift of the loop body: the four stored limbs sum to `(A + B) / 2` -/
theorem add_shr (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64)
    (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (hb3 : b3 < 2 ^ 64)
    (hlt : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) < 2 ^ 256) :
    ((BitVec.ofNat 64 (a1 + b1 + (a0 + b0) / 18446744073709551616) <<< 63) |||
        ((BitVec.ofNat 64 a0 + BitVec.ofNat 64 b0) >>> 1)).toNat +
      2 ^ 64 * ((BitVec.ofNat 64 (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616) <<< 63) |||
        (BitVec.ofNat 64 (a1 + b1 + (a0 + b0) / 18446744073709551616) >>> 1)).toNat +
      2 ^ 128 * ((BitVec.ofNat 64 (b3 + a3 + (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) <<< 63) |||
        (BitVec.ofNat 64 (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616) >>> 1)).toNat +
      2 ^ 192 * (BitVec.ofNat 64 (b3 + a3 + (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) >>> 1).toNat
    = ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
  rw [shr_limb, shr_limb, shr_limb]
  have e0 : (BitVec.ofNat 64 a0 + BitVec.ofNat 64 b0).toNat = (a0 + b0) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt hb0]
  have e1 : (BitVec.ofNat 64 (a1 + b1 + (a0 + b0) / 18446744073709551616)).toNat = (a1 + b1 + (a0 + b0) / 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_ofNat]
  have e2 : (BitVec.ofNat 64 (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616)).toNat =
      (a2 + b2 + (a1 + b1 + (a0 + b0) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_ofNat]
  rw [e0, e1, e2]
  have h3 : b3 + a3 + (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616 < 2 ^ 64 := by
    omega
  rw [shr_top _ h3]
  omega


theorem dec_toNat (n : Nat) (h : n < 2 * 2 ^ 64) : (decide (18446744073709551616 ≤ n)).toNat = n / 18446744073709551616 := by
  by_cases hc : 18446744073709551616 ≤ n
  · simp only [hc, decide_true, Bool.toNat_true]; omega
  · simp only [hc, decide_false, Bool.toNat_false]; omega

/-- `add_shr` in the exact form the executor produces (carries as `decide`) -/
theorem add_shr' (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64)
    (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (hb3 : b3 < 2 ^ 64)
    (hlt : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) < 2 ^ 256) :
    ((BitVec.ofNat 64 (a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat) <<< 63) |||
        ((BitVec.ofNat 64 a0 + BitVec.ofNat 64 b0) >>> 1)).toNat +
      18446744073709551616 * ((BitVec.ofNat 64 (a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat) <<< 63) |||
        (BitVec.ofNat 64 (a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat) >>> 1)).toNat +
      340282366920938463463374607431768211456 * ((BitVec.ofNat 64 (b3 + a3 + (decide (18446744073709551616 ≤ a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat)).toNat) <<< 63) |||
        (BitVec.ofNat 64 (a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat) >>> 1)).toNat +
      6277101735386680763835789423207666416102355444464034512896 * (BitVec.ofNat 64 (b3 + a3 + (decide (18446744073709551616 ≤ a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat)).toNat) >>> 1).toNat
    = ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
  have c1 : (decide (18446744073709551616 ≤ a0 + b0)).toNat = (a0 + b0) / 18446744073709551616 := dec_toNat _ (by omega)
  have c2 : (decide (18446744073709551616 ≤ a1 + b1 + (a0 + b0) / 18446744073709551616)).toNat =
      (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616 := dec_toNat _ (by omega)
  have c3 : (decide (18446744073709551616 ≤ a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616)).toNat =
      (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616 := dec_toNat _ (by omega)
  rw [c1, c2, c3]
  have := add_shr a0 a1 a2 a3 b0 b1 b2 b3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hlt
  simpa using this

end Fv256.SqrtLimb
