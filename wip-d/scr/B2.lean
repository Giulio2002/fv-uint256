import Janus

namespace Fv256.D

theorem or_add (a b k : Nat) (ha : a < 2 ^ k) : (a ||| b * 2 ^ k) = a + b * 2 ^ k := by
  have := Nat.two_pow_add_eq_or_of_lt ha b
  rw [Nat.or_comm, Nat.mul_comm b, Nat.add_comm, this]

theorem rot12 (y : Nat) (hy : y < 2 ^ 64) :
    ((BitVec.ofNat 64 y).rotateRight 12 &&& 18446744073709551615#64 &&& 4503599627370495#64).toNat = y / 4096 := by
  simp only [BitVec.toNat_and, BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy, Nat.reduceMod]
  have e1 : (18446744073709551615 : Nat) = 2 ^ 64 - 1 := by decide
  have e2 : (4503599627370495 : Nat) = 2 ^ 52 - 1 := by decide
  rw [e1, e2, Nat.mod_eq_of_lt (by decide : 2 ^ 64 - 1 < 2 ^ 64), Nat.mod_eq_of_lt (by decide : 2 ^ 52 - 1 < 2 ^ 64), Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  have h3 : y <<< (64 - 12) % 2 ^ 64 % 2 ^ 52 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.shiftLeft_eq]
    show y * 2 ^ 52 % 2 ^ 52 = 0
    simp
  have h4 : (y >>> 12) < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have h5 : (y >>> 12 ||| y <<< (64 - 12) % 2 ^ 64) < 2 ^ 64 :=
    Nat.or_lt_two_pow h4 (Nat.mod_lt _ (by omega))
  rw [Nat.mod_eq_of_lt h5, Nat.or_mod_two_pow, h3, Nat.or_zero, Nat.shiftRight_eq_div_pow]
  show y / 2 ^ 12 % 2 ^ 52 = y / 4096
  apply Nat.mod_eq_of_lt; omega

theorem rot52 (v : BitVec 64) : (v.rotateRight 52).toNat % 4096 = v.toNat / 2 ^ 52 := by
  have hv := v.isLt
  rw [BitVec.toNat_rotateRight, show (4096 : Nat) = 2 ^ 12 by decide]
  have h3 : v.toNat <<< (64 - 52 % 64) % 2 ^ 64 % 2 ^ 12 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.shiftLeft_eq]
    simp
  rw [Nat.or_mod_two_pow, h3, Nat.or_zero, Nat.shiftRight_eq_div_pow]
  show v.toNat / 2 ^ (52 % 64) % 2 ^ 12 = v.toNat / 2 ^ 52
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  simpa using hv


theorem form_val (F e : BitVec 64) (hF : F.toNat ≤ 2 ^ 52) (he : e.toNat ≤ 256) :
    ((if (F.rotateRight 52).toNat % 4096 = 0 then F else 0#64).toNat |||
        4503599627370496 * (if (F.rotateRight 52).toNat % 4096 = 0 then e + 1022#64 else e + 1023#64).toNat % 18446744073709551616)
      % 18446744073709551616 % 2 ^ 128 % 2 ^ 64 =
    if F.toNat / 2 ^ 52 ≠ 0 then (e.toNat + 1023) * 2 ^ 52 else (e.toNat + 1022) * 2 ^ 52 + F.toNat := by
  rw [rot52]
  have e1 : (e + 1022#64).toNat = e.toNat + 1022 := by
    rw [BitVec.toNat_add]; simp; omega
  have e2 : (e + 1023#64).toNat = e.toNat + 1023 := by
    rw [BitVec.toNat_add]; simp; omega
  by_cases c : F.toNat / 2 ^ 52 = 0
  · have hl : F.toNat < 2 ^ 52 := by
      rcases Nat.div_eq_zero_iff.1 c with h | h
      · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
      · exact h
    rw [if_pos c, if_pos c, e1, if_neg (by simpa using c), Nat.mul_comm 4503599627370496, show (4503599627370496 : Nat) = 2 ^ 52 by decide]
    rw [Nat.mod_eq_of_lt (by omega : (e.toNat + 1022) * 2 ^ 52 < 2 ^ 64), or_add _ _ _ hl]
    rw [Nat.add_comm]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
  · have h52 : F.toNat = 2 ^ 52 := by
      have : 2 ^ 52 ≤ F.toNat := by
        by_cases h : F.toNat < 2 ^ 52
        · exact absurd (Nat.div_eq_of_lt h) c
        · omega
      omega
    rw [if_neg c, if_neg c, e2, if_pos (by simpa using c)]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_or]
    rw [show (4503599627370496 : Nat) = 2 ^ 52 by decide, Nat.mul_comm]
    repeat rw [Nat.mod_eq_of_lt (by omega)]

end Fv256.D
