import Janus
set_option maxRecDepth 100000
theorem bv_dec (x : Nat) (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x - 1#64).toNat = (x + 2 ^ 64 - 1) % 2 ^ 64 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
theorem hdl (a b : Nat) : (decide (a < b)).toNat = if a < b then 1 else 0 := by split <;> simp_all
theorem hdl2 (a b : Nat) (hb : b ≤ 1) : (decide (a < b)).toNat = b - a := by
  rcases Nat.lt_or_ge a b with h | h
  · have : decide (a < b) = true := by simpa using h
    rw [this]; simp; omega
  · have : decide (a < b) = false := by simpa using h
    rw [this]; simp; omega
theorem wstep (w o bin : Nat) (hw : w < 2 ^ 64) (hb : bin ≤ 1) (ho : o = (w % 2 ^ 64 + 2 ^ 64 - 0 % 2 ^ 64 - bin) % 2 ^ 64) :
    o + bin = w + 2 ^ 64 * (bin - w) := by
  have h0 : (0 : Nat) % 2 ^ 64 = 0 := rfl
  rw [Nat.mod_eq_of_lt hw, h0] at ho
  omega
theorem sum5d (xb9frdx xb9fm60 xb9frbx xb9fm50 xb9fm48 xb9fm40 xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 : Nat)
  (c : xb9frdx < 2) (b0 : xb9fm60 < 2^64) (b1 : xb9frbx < 2^64) (b2 : xb9fm50 < 2^64) (b3 : xb9fm48 < 2^64) (b4 : xb9fm40 < 2^64)
  (h_xbedrdi : xbedrdi = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm60 else BitVec.ofNat 64 xb9fm60 - 1#64).toNat)
  (h_xbedr8 : xbedr8 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9frbx else BitVec.ofNat 64 ((xb9frbx % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm60 < 1)).toNat) % 18446744073709551616)).toNat)
  (h_xbedr10 : xbedr10 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm50 else BitVec.ofNat 64 ((xb9fm50 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat) % 18446744073709551616)).toNat)
  (h_xbedr12 : xbedr12 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm48 else BitVec.ofNat 64 ((xb9fm48 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm50 < (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat)).toNat) % 18446744073709551616)).toNat)
  (h_xbedr15 : xbedr15 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm40 else BitVec.ofNat 64 ((xb9fm40 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm48 < (decide (xb9fm50 < (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616)).toNat)
  : xbedrdi + 2^64 * xbedr8 + 2^128 * xbedr10 + 2^192 * xbedr12 + 2^256 * xbedr15
     + xb9frdx = (xb9fm60 + 2^64 * xb9frbx + 2^128 * xb9fm50 + 2^192 * xb9fm48 + 2^256 * xb9fm40) ∨
     (xb9fm60 = 0 ∧ xb9frbx = 0 ∧ xb9fm50 = 0 ∧ xb9fm48 = 0 ∧ xb9fm40 = 0 ∧ xb9frdx = 1 ∧ xbedrdi + 2^64 * xbedr8 + 2^128 * xbedr10 + 2^192 * xbedr12 + 2^256 * xbedr15 = 2^320 - 1) := by
  rcases Nat.lt_or_ge xb9frdx 1 with hc | hc
  · have h0 : xb9frdx = 0 := by omega
    subst h0
    simp only [if_true] at *
    simp only [BitVec.toNat_ofNat] at h_xbedrdi h_xbedr8 h_xbedr10 h_xbedr12 h_xbedr15
    left; omega
  · have h1 : xb9frdx = 1 := by omega
    subst h1
    simp only [Nat.one_ne_zero, ite_false] at h_xbedrdi h_xbedr8 h_xbedr10 h_xbedr12 h_xbedr15
    simp (disch := first | omega | exact Bool.toNat_le _) only [hdl2, BitVec.toNat_sub, BitVec.toNat_ofNat] at h_xbedrdi h_xbedr8 h_xbedr10 h_xbedr12 h_xbedr15
    have k1 := wstep xb9frbx xbedr8 (1 - xb9fm60) b1 (by omega) (by simpa using h_xbedr8)
    have k2 := wstep xb9fm50 xbedr10 (1 - xb9fm60 - xb9frbx) b2 (by omega) (by simpa using h_xbedr10)
    have k3 := wstep xb9fm48 xbedr12 (1 - xb9fm60 - xb9frbx - xb9fm50) b3 (by omega) (by simpa using h_xbedr12)
    have k4 := wstep xb9fm40 xbedr15 (1 - xb9fm60 - xb9frbx - xb9fm50 - xb9fm48) b4 (by omega) (by simpa using h_xbedr15)
    have k0 : xbedrdi + 1 = xb9fm60 + 2^64 * (1 - xb9fm60) := by clear k1 k2 k3 k4 h_xbedr8 h_xbedr10 h_xbedr12 h_xbedr15; omega
    clear h_xbedrdi h_xbedr8 h_xbedr10 h_xbedr12 h_xbedr15
    rcases Nat.eq_zero_or_pos (1 - xb9fm60 - xb9frbx - xb9fm50 - xb9fm48 - xb9fm40) with hz | hz
    · left; omega
    · right; omega
