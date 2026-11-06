import Fv256.Spec

/-!
# Mathematics of `math/bits.Div64` (ISA independent)

Pure `Nat` lemmas about the Knuth/Hacker's-Delight `divlu` digit step that Go's software 128/64 division uses
(two 32-bit quotient digits, each corrected by a bounded loop), and the assembly of the two digits into
`(hi * 2^64 + lo) / y`, `(hi * 2^64 + lo) % y`.  Written from the algorithm's mathematics, not from the machine code.
-/

namespace Fv256.D64

/-- The first estimate of a digit is at most `B + 1` (`B = 2^32`, `B <= 2 * yn1`). -/
theorem init_bound (B yn1 yn0 A : Nat) (h1 : B ≤ 2 * yn1) (h0 : yn0 < B) (hA : A < yn1 * B + yn0) :
    A / yn1 ≤ B + 1 := by
  have hp : 0 < yn1 := by omega
  have : A < yn1 * (B + 2) := by
    have e : yn1 * (B + 2) = yn1 * B + yn1 * 2 := by rw [Nat.mul_add]
    omega
  have := Nat.div_lt_of_lt_mul this
  omega

/-- A trial digit rejected by the correction loop condition is strictly above the true digit. -/
theorem step_gt (B yn1 yn0 A C q rhat : Nat) (hB : C < B) (hA : A < yn1 * B + yn0)
    (hI : q * yn1 + rhat = A) (hc : B ≤ q ∨ B * rhat + C < q * yn0) :
    (A * B + C) / (yn1 * B + yn0) < q := by
  rcases hc with hc | hc
  · have : (A * B + C) / (yn1 * B + yn0) < B := by
      apply Nat.div_lt_of_lt_mul
      have : (A + 1) * B ≤ (yn1 * B + yn0) * B := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul] at this
      omega
    omega
  · apply Nat.div_lt_of_lt_mul
    have e : (yn1 * B + yn0) * q = (q * yn1) * B + q * yn0 := by grind
    have e2 : A * B = (q * yn1) * B + rhat * B := by rw [← hI]; grind
    rw [e]
    have : B * rhat = rhat * B := Nat.mul_comm _ _
    omega

/-- The exit of the correction loop: the digit is exact. -/
theorem exit_eq (B yn1 yn0 A C q rhat : Nat) (hI : q * yn1 + rhat = A) (hge : (A * B + C) / (yn1 * B + yn0) ≤ q)
    (hc : q * yn0 ≤ B * rhat + C) (hy : 0 < yn1 * B + yn0) :
    q = (A * B + C) / (yn1 * B + yn0) := by
  apply Nat.le_antisymm _ hge
  rw [Nat.le_div_iff_mul_le hy]
  have e : q * (yn1 * B + yn0) = (q * yn1) * B + q * yn0 := by grind
  have e2 : A * B = (q * yn1) * B + rhat * B := by rw [← hI]; grind
  have : B * rhat = rhat * B := Nat.mul_comm _ _
  omega

/-- Exit by the `rhat >= B` break: the digit is exact too (needs `q <= B`). -/
theorem exit_break (B yn1 yn0 A C q rhat : Nat) (hI : q * yn1 + rhat = A)
    (hge : (A * B + C) / (yn1 * B + yn0) ≤ q) (hr : B ≤ rhat) (hq : q ≤ B)
    (h0 : yn0 < B) (hy : 0 < yn1 * B + yn0) :
    q = (A * B + C) / (yn1 * B + yn0) := by
  apply exit_eq B yn1 yn0 A C q rhat hI hge _ hy
  have : q * yn0 ≤ B * B := Nat.mul_le_mul hq (by omega)
  have : B * B ≤ B * rhat := Nat.mul_le_mul_left _ hr
  omega

/-- The first estimate `A / d1` is an upper bound on the true digit. -/
theorem est_ge (B d1 d0 A C : Nat) (hB : 0 < B) (hC : C < B) (hd1 : 0 < d1) :
    (A * B + C) / (d1 * B + d0) ≤ A / d1 := by
  have h1 : (A * B + C) / (d1 * B + d0) ≤ (A * B + C) / (d1 * B) :=
    Nat.div_le_div_left (by omega) (Nat.mul_pos hd1 hB)
  refine Nat.le_trans h1 ?_
  rw [Nat.le_div_iff_mul_le hd1]
  have h2 := Nat.div_mul_le_self (A * B + C) (d1 * B)
  have h3 : (A * B + C) / (d1 * B) * d1 * B ≤ A * B + C := by
    have : (A * B + C) / (d1 * B) * d1 * B = (A * B + C) / (d1 * B) * (d1 * B) := by grind
    omega
  have h4 : (A * B + C) / (d1 * B) * d1 * B < (A + 1) * B := by
    rw [Nat.add_mul]; omega
  have := Nat.lt_of_mul_lt_mul_right h4
  omega

/-- The remainder after a digit is exact is below the divisor and is what a 64-bit wrap-free subtraction gives. -/
theorem rem_lt (Y N : Nat) (hY : 0 < Y) : N - (N / Y) * Y < Y := by
  have := Nat.mod_lt N hY
  have := Nat.div_add_mod N Y
  have e : (N / Y) * Y = Y * (N / Y) := Nat.mul_comm _ _
  omega

/-- Assembly of the two digits. `s` is the normalisation shift. -/
theorem assemble (hi lo y s : Nat) (hy : 0 < y) (hys : y * 2 ^ s < 2 ^ 64) (hhi : hi < y) (hs : s < 64)
    (q1 q0 r1 r0 : Nat) (N1 N0 un32 un10 : Nat)
    (hu32 : un32 = hi * 2 ^ s + lo / 2 ^ (64 - s)) (hu10 : un10 = lo * 2 ^ s % 2 ^ 64)
    (hN1 : N1 = un32 * 2 ^ 32 + un10 / 2 ^ 32)
    (hq1 : q1 = N1 / (y * 2 ^ s)) (hr1 : r1 = N1 - q1 * (y * 2 ^ s))
    (hN0 : N0 = r1 * 2 ^ 32 + un10 % 2 ^ 32)
    (hq0 : q0 = N0 / (y * 2 ^ s)) (hr0 : r0 = N0 - q0 * (y * 2 ^ s)) :
    q1 * 2 ^ 32 + q0 = (hi * 2 ^ 64 + lo) / y ∧ r0 / 2 ^ s = (hi * 2 ^ 64 + lo) % y := by
  have hY : 0 < y * 2 ^ s := Nat.mul_pos hy (Nat.two_pow_pos s)
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  -- U * 2^s = un32 * 2^64 + un10
  have hlo : lo * 2 ^ s = (lo / 2 ^ (64 - s)) * 2 ^ 64 + un10 := by
    have e : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
    have hq : lo * 2 ^ s / 2 ^ 64 = lo / 2 ^ (64 - s) := by
      rw [e, Nat.mul_comm (2 ^ (64 - s)), ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hp]
    rw [hu10, ← hq]
    have := Nat.div_add_mod (lo * 2 ^ s) (2 ^ 64)
    omega
  have hU : (hi * 2 ^ 64 + lo) * 2 ^ s = un32 * 2 ^ 64 + un10 := by
    rw [hu32, Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ 64) (2 ^ s), ← Nat.mul_assoc, hlo]
    grind
  have h32 : un32 * 2 ^ 64 + un10 = (N1 * 2 ^ 32) + un10 % 2 ^ 32 := by
    have e1 : un10 = (un10 / 2 ^ 32) * 2 ^ 32 + un10 % 2 ^ 32 := by
      have := Nat.div_add_mod un10 (2 ^ 32)
      omega
    have e64 : 2 ^ 64 = 2 ^ 32 * 2 ^ 32 := by rw [← Nat.pow_add]
    rw [hN1, e64]
    grind
  -- N1 = q1 * Y + r1
  have hd1 : N1 = q1 * (y * 2 ^ s) + r1 := by
    have := Nat.div_mul_le_self N1 (y * 2 ^ s)
    rw [hr1, hq1]; omega
  have hd0 : N0 = q0 * (y * 2 ^ s) + r0 := by
    have := Nat.div_mul_le_self N0 (y * 2 ^ s)
    rw [hr0, hq0]; omega
  have hr0lt : r0 < y * 2 ^ s := by rw [hr0, hq0]; exact rem_lt _ _ hY
  have hT : (hi * 2 ^ 64 + lo) * 2 ^ s = (y * 2 ^ s) * (q1 * 2 ^ 32 + q0) + r0 := by
    have h1 : N1 * 2 ^ 32 + un10 % 2 ^ 32 = q1 * (y * 2 ^ s) * 2 ^ 32 + N0 := by
      rw [hd1, hN0]; grind
    rw [hU, h32, h1, hd0]
    grind
  have := norm_div (hi * 2 ^ 64 + lo) y (2 ^ s) (q1 * 2 ^ 32 + q0) r0 hp hy (by rw [hT]) hr0lt
  refine ⟨this.1, ?_⟩
  rw [this.2, Nat.mul_div_cancel _ hp]
where
  norm_div (U D t Q Rn : Nat) (ht : 0 < t) (hD : 0 < D) (h : U * t = D * t * Q + Rn) (hR : Rn < D * t) :
      Q = U / D ∧ Rn = (U % D) * t := by
    have h1 : D * Q * t ≤ U * t := by
      have : D * Q * t = D * t * Q := by grind
      omega
    have h2 : D * Q ≤ U := Nat.le_of_mul_le_mul_right h1 ht
    obtain ⟨r, hr⟩ : ∃ r, U = D * Q + r := ⟨U - D * Q, by omega⟩
    have h3 : Rn = r * t := by
      have : U * t = D * Q * t + r * t := by rw [hr]; grind
      have e : D * Q * t = D * t * Q := by grind
      omega
    have h4 : r < D := by
      have : r * t < D * t := by omega
      exact Nat.lt_of_mul_lt_mul_right this
    have hq := (Nat.div_mod_unique (a := U) (b := D) (d := Q) (c := r) hD).2 ⟨by omega, h4⟩
    obtain ⟨hq1, hq2⟩ := hq
    exact ⟨hq1.symm, by rw [hq2, h3]⟩

end Fv256.D64
