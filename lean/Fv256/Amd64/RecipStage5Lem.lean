namespace Fv256.Amd64.RecipSeg

theorem msb_iff (x : Nat) (hx : x < 2 ^ 64) : ((BitVec.ofNat 64 x).msb = true) ↔ 2 ^ 63 ≤ x := by
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, decide_eq_true_eq]

/-- the doubling segment `bed .. c49` as one equation: the five output words are `2 W mod 2^320` when `rcx` has its sign bit set, else `W` -/
theorem dbl5 (rcx d0 d1 d2 d3 d4 o0 o1 o2 o3 o4 : Nat)
    (hr : rcx < 2 ^ 64) (b0 : d0 < 2 ^ 64) (b1 : d1 < 2 ^ 64) (b2 : d2 < 2 ^ 64) (b3 : d3 < 2 ^ 64) (b4 : d4 < 2 ^ 64)
    (h0 : o0 = (if (BitVec.ofNat 64 rcx).msb = true then BitVec.ofNat 64 (d0 + d0) else BitVec.ofNat 64 d0).toNat)
    (h1 : o1 = (if (BitVec.ofNat 64 rcx).msb = true then BitVec.ofNat 64 (d1 + d1 + (d0 + d0) / 18446744073709551616) else BitVec.ofNat 64 d1).toNat)
    (h2 : o2 = (if (BitVec.ofNat 64 rcx).msb = true then BitVec.ofNat 64 (d2 + d2 + (d1 + d1 + (d0 + d0) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 d2).toNat)
    (h3 : o3 = (if (BitVec.ofNat 64 rcx).msb = true then BitVec.ofNat 64 (d3 + d3 + (d2 + d2 + (d1 + d1 + (d0 + d0) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 d3).toNat)
    (h4 : o4 = (if (BitVec.ofNat 64 rcx).msb = true then BitVec.ofNat 64 (d4 + d4 + (d3 + d3 + (d2 + d2 + (d1 + d1 + (d0 + d0) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 d4).toNat) :
    o0 + 2 ^ 64 * o1 + 2 ^ 128 * o2 + 2 ^ 192 * o3 + 2 ^ 256 * o4 =
      if 2 ^ 63 ≤ rcx then 2 * (d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * d4) % 2 ^ 320
      else d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * d4 := by
  by_cases hm : (BitVec.ofNat 64 rcx).msb = true
  · have hc : 2 ^ 63 ≤ rcx := (msb_iff rcx hr).1 hm
    rw [if_pos hc]
    simp only [hm, if_true, BitVec.toNat_ofNat] at h0 h1 h2 h3 h4
    omega
  · have hc : ¬ 2 ^ 63 ≤ rcx := fun h => hm ((msb_iff rcx hr).2 h)
    rw [if_neg hc]
    have hm' : (BitVec.ofNat 64 rcx).msb = false := by simpa using hm
    simp only [hm', Bool.false_eq_true, if_false, BitVec.toNat_ofNat] at h0 h1 h2 h3 h4
    omega

theorem stage5T_eq (w0 w1 w2 w3 w4 y0 y1 y2 y3 : Nat) :
    2 ^ 0 * (w0 * y0) + 2 ^ 64 * (w0 * y1 + w1 * y0) + 2 ^ 128 * (w0 * y2 + w1 * y1 + w2 * y0) + 2 ^ 192 * (w0 * y3 + w1 * y2 + w2 * y1 + w3 * y0) + 2 ^ 256 * (w1 * y3 + w2 * y2 + w3 * y1 + w4 * y0) + 2 ^ 320 * (w2 * y3 + w3 * y2 + w4 * y1) + 2 ^ 384 * (w3 * y3 + w4 * y2) + 2 ^ 448 * (w4 * y3) =
      (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4) * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
  simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm w0, Nat.mul_left_comm w1, Nat.mul_left_comm w2, Nat.mul_left_comm w3, Nat.mul_left_comm w4]
  omega

theorem r4step (W R4p Y c P : Nat) (hW : W < 2 ^ 320)
    (hd : W + c = R4p ∨ (R4p = 0 ∧ c = 1 ∧ W = 2 ^ 320 - 1))
    (hc : c = if 2 ^ 574 < P then 1 else 0) (hP : P = R4p * Y) :
    W = if 2 ^ 574 < R4p * Y then (R4p + 2 ^ 320 - 1) % 2 ^ 320 else R4p := by
  subst hP
  by_cases h : 2 ^ 574 < R4p * Y
  · rw [if_pos h]; rw [if_pos h] at hc; subst hc
    rcases hd with hd | ⟨h0, _, h2⟩
    · omega
    · omega
  · rw [if_neg h]; rw [if_neg h] at hc; subst hc
    rcases hd with hd | ⟨_, h1, _⟩
    · omega
    · omega

theorem cpy (c : Bool) (a b r m : Nat) (hb : b < 2 ^ 64)
    (gr : r = (if c = true then BitVec.ofNat 64 a else BitVec.ofNat 64 b).toNat)
    (gm : m = (if c = true then a % 2 ^ 64 else b) % 2 ^ 64) : m = r := by
  cases c
  · simp only [Bool.false_eq_true, if_false, BitVec.toNat_ofNat] at gr gm
    rw [gm, gr, Nat.mod_eq_of_lt hb]
  · simp only [if_true, BitVec.toNat_ofNat] at gr gm
    rw [gm, gr, Nat.mod_mod]

theorem rcx_dbl (rcx r : Nat) (hr : rcx < 2 ^ 64)
    (g : r = (if (BitVec.ofNat 64 rcx).msb = true then 0#64 else BitVec.ofNat 64 rcx).toNat) :
    r = if 2 ^ 63 ≤ rcx then 0 else rcx := by
  by_cases hm : (BitVec.ofNat 64 rcx).msb = true
  · have hc := (msb_iff rcx hr).1 hm
    rw [if_pos hc]; rw [if_pos hm] at g; simpa using g
  · have hc : ¬ 2 ^ 63 ≤ rcx := fun h => hm ((msb_iff rcx hr).2 h)
    rw [if_neg hc]; rw [if_neg hm] at g; simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr] using g

end Fv256.Amd64.RecipSeg
