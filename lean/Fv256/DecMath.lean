import Janus

namespace Fv256.E

theorem div100_nat (a : Nat) (h : a < 2^32) : a / 2 * 2748779070 / 137438953472 = a / 100 := by
  omega
theorem div100_64 (X : BitVec 64) (h : X.toNat < 2^32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 X) >>> 1 * 2748779070#64) >>> 37 = BitVec.ofNat 64 (X.toNat / 100) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.setWidth 64 (BitVec.setWidth 32 X) >>> 1).toNat = X.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega : X.toNat < 2^32), Nat.mod_eq_of_lt (by omega : X.toNat < 2^64)]
  have e2 : (2748779070#64).toNat = 2748779070 := by rfl
  have h2 := div100_nat X.toNat h
  have h3 : X.toNat / 2 * 2748779070 < 2^64 := by omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, e1, e2, Nat.mod_eq_of_lt h3,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have : X.toNat / 2 * 2748779070 / 2 ^ 37 = X.toNat / 100 := by simpa using h2
  rw [this]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem div100 (X : BitVec 64) (h : X.toNat < 2^32) :
    BitVec.setWidth 32 ((BitVec.setWidth 64 (BitVec.setWidth 32 X) >>> 1 * 2748779070#64) >>> 37) = BitVec.ofNat 32 (X.toNat / 100) := by
  rw [div100_64 X h]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : X.toNat / 100 < 2^32 := by omega
  rw [Nat.mod_eq_of_lt (by omega : X.toNat / 100 < 2^64)]


theorem div1e9_nat (u : Nat) (h : u < 2^64) : 9903520314283042200 * (u / 2) / 18446744073709551616 / 268435456 = u / 1000000000 := by
  omega

theorem div1e9 (u : Nat) (h : u < 2^64) :
    (BitVec.ofNat 64 (9903520314283042200 * (BitVec.ofNat 64 u >>> 1).toNat / 18446744073709551616) >>> 28) = BitVec.ofNat 64 (u / 1000000000) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 64 u >>> 1).toNat = u / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  have h2 : 9903520314283042200 * (u / 2) / 18446744073709551616 < 2 ^ 64 := by omega
  rw [e1, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2,
    Nat.shiftRight_eq_div_pow]
  have := div1e9_nat u h
  rw [show (2:Nat)^28 = 268435456 by rfl, this]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem mod1e9 (u : Nat) (h : u < 2^64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 (u / 1000000000) * 1000000000#64 = BitVec.ofNat 64 (u % 1000000000) := by
  apply BitVec.eq_of_toNat_eq
  have t1 : (BitVec.ofNat 64 u).toNat = u := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  have t2 : (BitVec.ofNat 64 (u / 1000000000)).toNat = u / 1000000000 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have t3 : (1000000000#64).toNat = 1000000000 := rfl
  have t4 : (BitVec.ofNat 64 (u % 1000000000)).toNat = u % 1000000000 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3 : u / 1000000000 * 1000000000 < 2^64 := by omega
  rw [BitVec.toNat_sub, BitVec.toNat_mul, t1, t2, t3, t4, Nat.mod_eq_of_lt h3]
  omega



/-! arm64 normal forms of the `/100` and `/1e9` sequences (UBFX/LSR become `rotateRight` and masks) -/
theorem q1 (n : Nat) (h : n < 2^32) :
    ((BitVec.ofNat 64 n).rotateRight 1 &&& 9223372039002259455#64 &&& 2147483647#64) = BitVec.ofNat 64 (n/2) := by
  apply BitVec.eq_of_toNat_eq
  have hn : n % 2^64 = n := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_rotateRight, BitVec.toNat_ofNat, hn, Nat.and_assoc]
  have hAB : (9223372039002259455#64).toNat &&& (2147483647#64).toNat = 2^31 - 1 := by decide
  rw [hAB, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_one]
  have e1 : n * 2 ^ (64 - 1) % 2 ^ 64 = (n % 2) * 2^63 := by omega
  rw [e1, Nat.mod_eq_of_lt (by omega : n / 2 < 2 ^ 64)]
  have e2 : (n / 2 ||| (n % 2) * 2^63) = (n % 2) * 2^63 + n / 2 := by
    rw [Nat.or_comm, Nat.mul_comm (n % 2) (2^63)]
    exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
  rw [e2]
  have hm : n / 2 < 2^31 := by omega
  have e3 : (n % 2) * 2^63 + n / 2 = n / 2 + 2^31 * ((n % 2) * 2^32) := by
    have : (2:Nat)^63 = 2^31 * 2^32 := by rw [← Nat.pow_add]
    rw [this]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]
  rw [e3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]

set_option maxRecDepth 100000 in
theorem q2 (n : Nat) (h : n < 2^32) :
    ((BitVec.ofNat 64 (n/2) * 2748779070#64).rotateRight 37 &&& 18446744073709551615#64 &&& 134217727#64) = BitVec.ofNat 64 (n/100) := by
  apply BitVec.eq_of_toNat_eq
  have hv : n / 2 < 2^31 := by omega
  have hp : n / 2 * 2748779070 < 2^63 := by omega
  have hC : (2748779070#64).toNat = 2748779070 := rfl
  have hm : (BitVec.ofNat 64 (n/2) * 2748779070#64).toNat = n / 2 * 2748779070 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hC, Nat.mod_eq_of_lt (by omega : n / 2 < 2^64)]
    exact Nat.mod_eq_of_lt (by omega)
  have hAll : (18446744073709551615#64).toNat = 2^64 - 1 := rfl
  have hD : (134217727#64).toNat = 2^27 - 1 := rfl
  rw [BitVec.toNat_and, BitVec.toNat_and, hAll, hD, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_rotateRight, hm, BitVec.toNat_ofNat]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have e37 : (2:Nat) ^ 37 = 137438953472 := by decide
  have e27 : (2:Nat) ^ 27 = 134217728 := by decide
  have e64 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  have e63 : (2:Nat) ^ 63 = 9223372036854775808 := by decide
  have e2737 : (2:Nat) ^ (64 - 37) = 134217728 := by decide
  rw [e37, e27, e64, e2737] at *
  have hd100 : n / 2 * 2748779070 / 137438953472 = n / 100 := by omega
  obtain ⟨p, hpe⟩ : ∃ p, p = n / 2 * 2748779070 := ⟨_, rfl⟩
  rw [← hpe] at hp hd100 ⊢
  have hq : p / 137438953472 < 67108864 := by omega
  have h27 : (p * 134217728 % 18446744073709551616) % 134217728 = 0 := by omega
  have hlt : (p / 137438953472 ||| p * 134217728 % 18446744073709551616) < 18446744073709551616 := by
    have := Nat.or_lt_two_pow (x := p / 137438953472) (y := p * 134217728 % 18446744073709551616) (n := 64) (by omega) (by omega)
    simpa [e64] using this
  rw [Nat.mod_eq_of_lt hlt]
  have e27' : (134217728 : Nat) = 2 ^ 27 := by decide
  rw [e27', Nat.or_mod_two_pow, ← e27', h27, Nat.or_zero, Nat.mod_eq_of_lt (by omega : p / 137438953472 < 134217728), hd100,
    Nat.mod_eq_of_lt (by omega : n / 100 < 18446744073709551616)]

theorem q3a (x : Nat) (h : x < 2^32) :
    BitVec.setWidth 32 (BitVec.ofNat 64 x) - BitVec.setWidth 32 (BitVec.ofNat 64 (x/100)) * 100#32 = BitVec.ofNat 32 (x % 100) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.setWidth 32 (BitVec.ofNat 64 x)).toNat = x := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2^64), Nat.mod_eq_of_lt h]
  have h2 : (BitVec.setWidth 32 (BitVec.ofNat 64 (x/100))).toNat = x / 100 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x / 100 < 2^64), Nat.mod_eq_of_lt (by omega)]
  have h3 : (100#32).toNat = 100 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_mul, h1, h2, h3, BitVec.toNat_ofNat]
  have : x / 100 * 100 < 2^32 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

theorem q3 (v : Nat) (h : v < 100) :
    ((BitVec.setWidth 64 (BitVec.ofNat 32 v)).rotateRight 63).toNat &&& 4294967294 = 2 * v := by
  have e : ((BitVec.setWidth 64 (BitVec.ofNat 32 v)).toNat) = v := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_rotateRight, e]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have e1 : v / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
  have e2 : v * 2 ^ (64 - 63) % 2 ^ 64 = 2 * v := by omega
  rw [e1, e2, Nat.zero_or]
  have key : ∀ w, w < 100 → (2 * w) &&& 4294967294 = 2 * w := by decide +kernel
  exact key v h


theorem q4 (v : Nat) (h : v < 100) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 v) + BitVec.setWidth 64 (BitVec.ofNat 32 v) + 1#64)) = BitVec.ofNat 64 (2 * v + 1) := by
  have e : (BitVec.setWidth 64 (BitVec.ofNat 32 v)) = BitVec.ofNat 64 v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2^32), Nat.mod_eq_of_lt (by omega : v < 2^64)]
  have e2 : BitVec.ofNat 64 v + BitVec.ofNat 64 v + 1#64 = BitVec.ofNat 64 (2 * v + 1) := by
    apply BitVec.eq_of_toNat_eq
    have e1 : (1#64).toNat = 1 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2^64)]
    rw [Nat.mod_eq_of_lt (by omega : v + v < 2^64), Nat.mod_eq_of_lt (by omega : v + v + 1 < 2^64), Nat.mod_eq_of_lt (by omega : 2 * v + 1 < 2^64)]
    omega
  rw [e, e2]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2 * v + 1 < 2^64), Nat.mod_eq_of_lt (by omega : 2 * v + 1 < 2^32), Nat.mod_eq_of_lt (by omega : 2 * v + 1 < 2^64)]


theorem pow100 (j : Nat) : (100:Nat) ^ j = 10 ^ (2 * j) := by
  rw [Nat.pow_mul]

theorem dig_lo (x0 j : Nat) : x0 / 100 ^ j % 100 % 10 = x0 / 10 ^ (2 * j) % 10 := by
  rw [pow100]; generalize x0 / 10 ^ (2 * j) = a; omega

theorem dig_hi (x0 j : Nat) : x0 / 100 ^ j % 100 / 10 = x0 / 10 ^ (2 * j + 1) % 10 := by
  rw [pow100, Nat.pow_succ, ← Nat.div_div_eq_div_mul]; generalize x0 / 10 ^ (2 * j) = a; omega



theorem rot_lsr (u k : Nat) (hu : u < 2^64) (hk : 0 < k) (hk2 : k < 64) :
    ((BitVec.ofNat 64 u).rotateRight k).toNat % 2 ^ (64 - k) = u / 2 ^ k := by
  rw [BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt (by omega : k < 64)]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hlt : u / 2 ^ k < 2 ^ (64 - k) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    have : 64 - k + k = 64 := by omega
    rw [this]; exact hu
  have hlo : (u * 2 ^ (64 - k)) % 2 ^ 64 % 2 ^ (64 - k) = 0 := by
    have : 2 ^ (64 - k) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    rw [Nat.mod_mod_of_dvd _ this]
    exact Nat.mul_mod_left _ _
  have e : (2:Nat) ^ (64 - k) = 2 ^ (64 - k) := rfl
  rw [show (2:Nat)^(64-k) = 2^(64-k) from rfl]
  rw [Nat.or_mod_two_pow, hlo, Nat.or_zero, Nat.mod_eq_of_lt hlt]


theorem p1 (u : Nat) (hu : u < 2^64) :
    ((BitVec.ofNat 64 u).rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64) = BitVec.ofNat 64 (u/2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  have e1 : (18446744073709551615#64).toNat = 2^64 - 1 := rfl
  have e2 : (9223372036854775807#64).toNat = 2^63 - 1 := rfl
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_one]
  have e3 : u * 2 ^ (64 - 1) % 2 ^ 64 = (u % 2) * 2^63 := by omega
  have e4 : (u / 2 ||| (u % 2) * 2^63) = u / 2 + (u % 2) * 2^63 := by
    rw [Nat.or_comm, Nat.mul_comm (u % 2) (2^63)]
    exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm.trans (by rw [Nat.add_comm])
  rw [e3, e4]
  have hm : u / 2 < 2^63 := by omega
  have e5 : (u / 2 + (u % 2) * 2^63) % 2^63 = u / 2 := by omega
  rw [Nat.mod_eq_of_lt (by omega : u / 2 + (u % 2) * 2^63 < 2^64), e5, Nat.mod_eq_of_lt (by omega : u / 2 < 2^64)]

theorem p3 (u : Nat) (hu : u < 2^64) :
    BitVec.ofNat 64 u - 1000000000#64 * BitVec.ofNat 64 (u / 10^9) = BitVec.ofNat 64 (u % 10^9) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 u).toNat = u := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  have h2 : (BitVec.ofNat 64 (u / 10^9)).toNat = u / 10^9 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3 : (1000000000#64).toNat = 10^9 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_mul, h1, h2, h3, BitVec.toNat_ofNat]
  have : 10^9 * (u / 10^9) < 2^64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega : u % 10^9 < 2^64)]
  omega

theorem p2 (u : Nat) (hu : u < 2^64) :
    ((BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 (u/2)) * 9903520314283042200#128)).rotateRight 28 &&&
      18446744073709551615#64 &&& 68719476735#64) = BitVec.ofNat 64 (u / 10^9) := by
  apply BitVec.eq_of_toNat_eq
  have hv : u / 2 < 2^63 := by omega
  have hw : (BitVec.setWidth 128 (BitVec.ofNat 64 (u/2))).toNat = u / 2 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u / 2 < 2^64), Nat.mod_eq_of_lt (by omega)]
  have hC : (9903520314283042200#128).toNat = 9903520314283042200 := rfl
  have hprod : (BitVec.setWidth 128 (BitVec.ofNat 64 (u/2)) * 9903520314283042200#128).toNat = u / 2 * 9903520314283042200 := by
    rw [BitVec.toNat_mul, hw, hC]
    exact Nat.mod_eq_of_lt (by omega)
  have hex : (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 (u/2)) * 9903520314283042200#128)).toNat = u / 2 * 9903520314283042200 / 2^64 := by
    rw [BitVec.extractLsb'_toNat, hprod]
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have e1 : (18446744073709551615#64).toNat = 2^64 - 1 := rfl
  have e2 : (68719476735#64).toNat = 2^36 - 1 := rfl
  rw [BitVec.toNat_and, BitVec.toNat_and, e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_rotateRight, hex, BitVec.toNat_ofNat]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  obtain ⟨h, hh⟩ : ∃ h, h = u / 2 * 9903520314283042200 / 2^64 := ⟨_, rfl⟩
  have hlt : h < 2^63 := by omega
  have hq : h / 2^28 = u / 10^9 := by omega
  rw [← hh]
  have hlt2 : h / 2^28 < 2^36 := by omega
  have hlo : (h * 2 ^ (64 - 28)) % 2 ^ 64 % 2 ^ 36 = 0 := by
    have : 2 ^ 36 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    rw [Nat.mod_mod_of_dvd _ this]
    exact Nat.mul_mod_left _ _
  have hlt3 : (h / 2^28 ||| h * 2 ^ (64 - 28) % 2 ^ 64) < 2 ^ 64 := Nat.or_lt_two_pow (by omega) (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt hlt3, Nat.or_mod_two_pow, hlo, Nat.or_zero, Nat.mod_eq_of_lt hlt2, hq]
  omega


theorem q5 (v : Nat) (h : v < 100) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 v + BitVec.ofNat 64 (v + 1))) = BitVec.ofNat 64 (2 * v + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v < 2^64), Nat.mod_eq_of_lt (by omega : v + 1 < 2^64), Nat.mod_eq_of_lt (by omega : v + (v + 1) < 2^64),
    Nat.mod_eq_of_lt (by omega : v + (v + 1) < 2^32), Nat.mod_eq_of_lt (by omega : 2 * v + 1 < 2^64)]
  omega


theorem dig9 (u k : Nat) (hk : k < 9) : u % 1000000000 / 10 ^ k % 10 = u / 10 ^ k % 10 := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow] <;> omega


end Fv256.E
