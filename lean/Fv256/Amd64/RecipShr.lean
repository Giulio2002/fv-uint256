namespace Fv256.Amd64.RecipSeg

theorem or_lo_hi (u v k : Nat) (hu : u < 2 ^ k) : u ||| 2 ^ k * v = u + 2 ^ k * v := by
  rw [Nat.or_comm, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hu]

theorem shl_mod (a n : Nat) (h1 : 1 ≤ n) (h2 : n < 64) :
    (a <<< (64 - n)) % 2 ^ 64 = 2 ^ (64 - n) * (a % 2 ^ n) := by
  have h : (2:Nat) ^ 64 = 2 ^ (64 - n) * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.shiftLeft_eq, h, Nat.mul_comm a, Nat.mul_mod_mul_left, Nat.mul_comm]

/-- one word of the 320-bit right shift by `n` -/
theorem shr_word (a b n : Nat) (h1 : 1 ≤ n) (h2 : n < 64) (ha : a < 2 ^ 64) :
    (a >>> n) ||| ((b <<< (64 - n)) % 2 ^ 64) = a / 2 ^ n + 2 ^ (64 - n) * (b % 2 ^ n) := by
  rw [shl_mod b n h1 h2, Nat.shiftRight_eq_div_pow]
  apply or_lo_hi
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n), ← Nat.pow_add]
  have : 64 - n + n = 64 := by omega
  rw [this]; exact ha

theorem shr5 (n a0 a1 a2 a3 a4 : Nat) (h1 : 1 ≤ n) (h2 : n < 64)
    (b0 : a0 < 2 ^ 64) (b1 : a1 < 2 ^ 64) (b2 : a2 < 2 ^ 64) (b3 : a3 < 2 ^ 64) (b4 : a4 < 2 ^ 64) :
    ((a0 >>> n) ||| ((a1 <<< (64 - n)) % 2 ^ 64)) + 2 ^ 64 * ((a1 >>> n) ||| ((a2 <<< (64 - n)) % 2 ^ 64)) +
      2 ^ 128 * ((a2 >>> n) ||| ((a3 <<< (64 - n)) % 2 ^ 64)) + 2 ^ 192 * ((a3 >>> n) ||| ((a4 <<< (64 - n)) % 2 ^ 64)) +
      2 ^ 256 * (a4 >>> n) = (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4) / 2 ^ n := by
  rw [shr_word a0 a1 n h1 h2 b0, shr_word a1 a2 n h1 h2 b1, shr_word a2 a3 n h1 h2 b2, shr_word a3 a4 n h1 h2 b3,
    Nat.shiftRight_eq_div_pow]
  have hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨ n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨ n = 55 ∨ n = 56 ∨ n = 57 ∨ n = 58 ∨ n = 59 ∨ n = 60 ∨ n = 61 ∨ n = 62 ∨ n = 63 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem tw (a b n : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h1 : 1 ≤ n) (h2 : n < 64) :
    (BitVec.ofNat 64 a >>> n ||| BitVec.ofNat 64 b <<< (64 - n) &&& 18446744073709551615#64).toNat =
      (a >>> n) ||| ((b <<< (64 - n)) % 2 ^ 64) := by
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have h : (18446744073709551615 % 2 ^ 64 : Nat) = 2 ^ 64 - 1 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

theorem tw' (a b n : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h1 : 1 ≤ n) (h2 : n < 64) :
    (BitVec.ofNat 64 b <<< (64 - n) &&& 18446744073709551615#64 ||| BitVec.ofNat 64 a >>> n).toNat =
      (a >>> n) ||| ((b <<< (64 - n)) % 2 ^ 64) := by
  rw [← tw a b n ha hb h1 h2]
  simp only [BitVec.toNat_or]
  rw [Nat.or_comm]

theorem tw_lt (a b n : Nat) (ha : a < 2 ^ 64) :
    (a >>> n) ||| ((b <<< (64 - n)) % 2 ^ 64) < 2 ^ 64 :=
  Nat.or_lt_two_pow (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)
    (Nat.mod_lt _ (by decide))

theorem tw4 (a n : Nat) (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a >>> n).toNat = a >>> n := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

end Fv256.Amd64.RecipSeg
