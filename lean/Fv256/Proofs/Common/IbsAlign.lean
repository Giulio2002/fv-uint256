import Janus

namespace Fv256.IndexByte64
open Janus Janus.Arm64

theorem nat_and31 (x : Nat) : x &&& 31 = x % 32 := by
  rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem nat_and_hi (x : Nat) (hx : x < 2 ^ 64) : x &&& 18446744073709551584 = x / 32 * 32 := by
  rw [show (18446744073709551584 : Nat) = (2 ^ 59 - 1) * 2 ^ 5 from rfl]
  rw [show (32 : Nat) = 2 ^ 5 from rfl]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hj : 5 ≤ j
  · by_cases hj' : j < 64
    · rw [show j - 5 + 5 = j by omega]; simp [hj, show j - 5 < 59 by omega]
    · have : x.testBit j = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [show j - 5 + 5 = j by omega]; simp [this]
  · simp [hj]

theorem bv_and31 (p : BitVec 64) : p &&& 31#64 = BitVec.ofNat 64 (p.toNat % 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [nat_and31]
  have := Nat.mod_lt p.toNat (show 32 > 0 by decide)
  rw [Nat.mod_eq_of_lt (by omega : p.toNat % 32 < 2 ^ 64)]

theorem bv_and_hi (p : BitVec 64) : p &&& 18446744073709551584#64 = BitVec.ofNat 64 (p.toNat / 32 * 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [nat_and_hi _ p.isLt]
  have := p.isLt
  rw [Nat.mod_eq_of_lt (by omega : p.toNat / 32 * 32 < 2 ^ 64)]

theorem ls_iff (n : BitVec 64) (o : Nat) (ho1 : 1 ≤ o) (ho2 : o < 32) (hn : n.toNat ≤ 2 ^ 48) :
    (((addWithCarry n (BitVec.ofNat 64 o - 32#64) false).snd.c &&
      !(addWithCarry n (BitVec.ofNat 64 o - 32#64) false).snd.z) = false) ↔ n.toNat ≤ 32 - o := by
  have ho' : (BitVec.ofNat 64 o).toNat = o := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hy : (BitVec.ofNat 64 o - 32#64).toNat = 18446744073709551616 - 32 + o := by
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    rw [BitVec.toNat_sub, ho', h32]
    simp only [Nat.reducePow]
    omega
  simp only [addWithCarry, hy, Bool.toNat_false, Nat.add_zero]
  have hR : (BitVec.ofNat 64 (n.toNat + (18446744073709551616 - 32 + o))).toNat = (n.toNat + o + 18446744073709551584) % 18446744073709551616 := by
    rw [BitVec.toNat_ofNat]; congr 1; omega
  by_cases h1 : n.toNat + o < 32
  · have : (BitVec.ofNat 64 (n.toNat + (18446744073709551616 - 32 + o))).toNat = n.toNat + (18446744073709551616 - 32 + o) := by
      rw [hR]; omega
    simp [this]; omega
  · by_cases h2 : n.toNat + o = 32
    · have hz : BitVec.ofNat 64 (n.toNat + (18446744073709551616 - 32 + o)) = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [hR]; simp; omega
      simp [hz]; omega
    · have hz : ¬ BitVec.ofNat 64 (n.toNat + (18446744073709551616 - 32 + o)) = 0 := by
        intro h
        have := congrArg BitVec.toNat h
        rw [hR] at this; simp at this; omega
      have : (BitVec.ofNat 64 (n.toNat + (18446744073709551616 - 32 + o))).toNat ≠ n.toNat + (18446744073709551616 - 32 + o) := by
        rw [hR, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      have e1 := decide_eq_true this
      have e2 := decide_eq_false hz
      simp only [e1, e2]
      simp; omega

end Fv256.IndexByte64
