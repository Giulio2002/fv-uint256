import Fv256.Proofs.Common.SpecF

/-!
# Barrett-reduction arithmetic of `MulMod` (`reduce4`), pure `Nat`, Extracted-free

`uint256.reduce4` reduces a 512-bit `x` modulo a four-word `m` with an approximation `mu` of `⌊(2^512-1)/m⌋` (`RecipOK`):
`q1 = ⌊x / 2^192⌋`, `q3 ≈ ⌊q1 * mu / 2^320⌋`, `r = x - q3 * m` (computed modulo `2^320`), `r += m` on a borrow, then `r -= m` while `r ≥ m`.
-/

namespace Fv256.F

/-- the Barrett quotient estimate is never too large and at most 5 too small (for any `mu` in the `RecipWeak` window) -/
theorem barrett_bounds (x m mu : Nat) (hx : x < 2 ^ 512) (hm1 : 2 ^ 192 ≤ m) (hm2 : m < 2 ^ 256) (hmu : RecipWeak m mu) :
    (x / 2 ^ 192 * mu / 2 ^ 320) * m ≤ x ∧ x < (x / 2 ^ 192 * mu / 2 ^ 320 + 6) * m := by
  obtain ⟨hlo, hhi⟩ := hmu
  unfold recipExact at hlo hhi
  have hm0 : 0 < m := by omega
  obtain ⟨M, hM⟩ : ∃ M : Nat, M = 2 ^ 192 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Nat, N = 2 ^ 320 := ⟨_, rfl⟩
  rw [← hM] at hm1
  rw [← hM, ← hN]
  have hB : 2 ^ 512 = M * N := by rw [hM, hN, ← Nat.pow_add]
  obtain ⟨q1, hq1⟩ : ∃ q1 : Nat, q1 = x / M := ⟨_, rfl⟩
  rw [← hq1]
  obtain ⟨qh, hqh⟩ : ∃ qh : Nat, qh = q1 * mu / N := ⟨_, rfl⟩
  rw [← hqh]
  have hq1lt : q1 < N := by
    rw [hq1, Nat.div_lt_iff_lt_mul (by rw [hM]; exact Nat.two_pow_pos _)]
    rw [show N * M = 2 ^ 512 by rw [Nat.mul_comm]; exact hB.symm]; exact hx
  have hq1le : q1 * M ≤ x := by rw [hq1]; exact Nat.div_mul_le_self x M
  have hq1gt : x < q1 * M + M := by
    have := Nat.lt_div_mul_add (a := x) (b := M) (by rw [hM]; exact Nat.two_pow_pos _)
    rw [← hq1] at this
    omega
  -- mu * m ≤ 2^512
  have hmu1 : mu * m ≤ M * N := by
    have h1 : mu * m ≤ (2 ^ 512 - 1) / m * m := Nat.mul_le_mul_right m hhi
    have h2 : (2 ^ 512 - 1) / m * m ≤ 2 ^ 512 - 1 := Nat.div_mul_le_self _ _
    have : 0 < 2 ^ 512 := Nat.two_pow_pos _
    omega
  have hmu2 : M * N ≤ (mu + 4) * m := by
    have h1 : (2 ^ 512 - 1) / m * m + m > 2 ^ 512 - 1 := by
      have := Nat.lt_div_mul_add (a := 2 ^ 512 - 1) (b := m) hm0
      omega
    have h2 : (2 ^ 512 - 1) / m ≤ mu + 3 := by omega
    have h3 : (2 ^ 512 - 1) / m * m ≤ (mu + 3) * m := Nat.mul_le_mul_right m h2
    have : (mu + 3) * m = mu * m + 3 * m := by rw [Nat.add_mul]
    have h4 : (mu + 4) * m = mu * m + 4 * m := by rw [Nat.add_mul]
    omega
  have hN0 : 0 < N := by rw [hN]; exact Nat.two_pow_pos _
  constructor
  · -- upper
    have h1 : qh * N ≤ q1 * mu := by rw [hqh]; exact Nat.div_mul_le_self _ _
    have : qh * m * N ≤ (q1 * M) * N := by
      calc qh * m * N = qh * N * m := by rw [Nat.mul_right_comm]
        _ ≤ q1 * mu * m := Nat.mul_le_mul_right m h1
        _ = q1 * (mu * m) := Nat.mul_assoc _ _ _
        _ ≤ q1 * (M * N) := Nat.mul_le_mul_left _ hmu1
        _ = (q1 * M) * N := by rw [Nat.mul_assoc]
    have := Nat.le_of_mul_le_mul_right this hN0
    omega
  · -- lower
    have h1 : q1 * mu < (qh + 1) * N := by
      have := Nat.lt_div_mul_add (a := q1 * mu) (b := N) hN0
      rw [← hqh] at this
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (qh + 1) * N * m > q1 * mu * m := by
      have := Nat.mul_lt_mul_of_pos_right h1 hm0
      omega
    -- q1 * (M*N) ≤ q1 * ((mu+2) m)
    have h3 : q1 * (M * N) ≤ q1 * mu * m + q1 * (4 * m) := by
      calc q1 * (M * N) ≤ q1 * ((mu + 4) * m) := Nat.mul_le_mul_left _ hmu2
        _ = q1 * mu * m + q1 * (4 * m) := by rw [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    have h4 : q1 * (4 * m) < 4 * m * N := by
      rw [Nat.mul_comm q1]
      exact Nat.mul_lt_mul_of_pos_left hq1lt (by omega)
    have h5 : (q1 * M) * N < ((qh + 1) * m + 4 * m) * N := by
      have e1 : (q1 * M) * N = q1 * (M * N) := Nat.mul_assoc _ _ _
      have e2 : ((qh + 1) * m + 4 * m) * N = (qh + 1) * N * m + 4 * m * N := by
        rw [Nat.add_mul, Nat.mul_right_comm]
      rw [e1, e2]; omega
    have h6 := Nat.lt_of_mul_lt_mul_right h5
    have : M ≤ m := hm1
    have h7 : (qh + 6) * m = (qh + 1) * m + 4 * m + m := by
      rw [show qh + 6 = (qh + 1) + 4 + 1 by omega, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega

/-- the 320-bit remainder after `r1 - r2` and the borrow correction -/
def reduceR (x m q : Nat) : Nat :=
  let a := x % 2 ^ 320
  let b := q * m % 2 ^ 320
  let r0 := (a + 2 ^ 320 - b) % 2 ^ 320
  if a < b then r0 + m else r0

/-- if the quotient estimate `q` is at most `k - 1` too small (`k ≤ 2^63`), the 320-bit remainder (plus one `m` after a borrow)
is congruent to `x` modulo `m` and still below `2^320` (so the final `while r ≥ m: r -= m` loop yields `x mod m`). -/
theorem reduceR_spec (x m q k : Nat) (hx : x < 2 ^ 512) (hm1 : 2 ^ 192 ≤ m) (hm2 : m < 2 ^ 256) (hk : k ≤ 2 ^ 63)
    (hq1 : q * m ≤ x) (hq2 : x < (q + k) * m) :
    reduceR x m q < 2 ^ 320 ∧ reduceR x m q % m = x % m := by
  have hm0 : 0 < m := by omega
  have hd : x - q * m < k * m := by
    have : (q + k) * m = q * m + k * m := by rw [Nat.add_mul]
    omega
  have hkm : k * m + m ≤ 2 ^ 320 - 1 := by
    have h1 : k * m ≤ 2 ^ 63 * m := Nat.mul_le_mul_right m hk
    have h2 : 2 ^ 63 * m ≤ 2 ^ 63 * 2 ^ 256 := Nat.mul_le_mul_left _ (Nat.le_of_lt hm2)
    have h3 : 2 ^ 63 * 2 ^ 256 = 2 ^ 319 := by rw [← Nat.pow_add]
    have h4 : 2 ^ 319 + 2 ^ 256 + 1 ≤ 2 ^ 320 := by decide
    omega
  obtain ⟨d, hdd⟩ : ∃ d, d = x - q * m := ⟨_, rfl⟩
  have hxd : x = q * m + d := by omega
  have hdlt : d + m < 2 ^ 320 := by omega
  have e1 : (x % 2 ^ 320 + 2 ^ 320 - q * m % 2 ^ 320) % 2 ^ 320 = d := by
    rw [hxd]
    omega
  unfold reduceR
  simp only []
  by_cases hab : x % 2 ^ 320 < q * m % 2 ^ 320
  · rw [if_pos hab, e1]
    refine ⟨by omega, ?_⟩
    rw [Nat.add_mod_right, hxd, Nat.mul_comm q m, Nat.mul_add_mod]
  · rw [if_neg hab, e1]
    refine ⟨by omega, ?_⟩
    rw [hxd, Nat.mul_comm q m, Nat.mul_add_mod]

/-- truncating the low partial products of the product `P` to `T ≤ P < T + N` loses at most one unit of `⌊P / N⌋` -/
theorem trunc_est (P T N : Nat) (hN : 0 < N) (h1 : T ≤ P) (h2 : P < T + N) :
    T / N ≤ P / N ∧ P / N ≤ T / N + 1 := by
  have a1 : N * (T / N) + T % N = T := Nat.div_add_mod T N
  have a2 : N * (P / N) + P % N = P := Nat.div_add_mod P N
  have b1 := Nat.mod_lt T hN
  have b2 := Nat.mod_lt P hN
  constructor
  · exact Nat.div_le_div_right h1
  · refine Nat.le_of_not_lt (fun hc => ?_)
    have hc' : T / N + 2 ≤ P / N := by omega
    have : N * (T / N + 2) ≤ N * (P / N) := Nat.mul_le_mul_left N hc'
    rw [Nat.mul_add] at this
    omega

/-- the whole estimate chain: if the code's quotient `q` is the exact Barrett value or one less, the remainder is correct -/
theorem reduce_value (x m mu q : Nat) (hx : x < 2 ^ 512) (hm1 : 2 ^ 192 ≤ m) (hm2 : m < 2 ^ 256) (hmu : RecipWeak m mu)
    (hq1 : x / 2 ^ 192 * mu / 2 ^ 320 ≤ q + 1) (hq2 : q ≤ x / 2 ^ 192 * mu / 2 ^ 320) :
    reduceR x m q < 2 ^ 320 ∧ reduceR x m q % m = x % m := by
  obtain ⟨b1, b2⟩ := barrett_bounds x m mu hx hm1 hm2 hmu
  refine reduceR_spec x m q 7 hx hm1 hm2 (by decide) ?_ ?_
  · exact Nat.le_trans (Nat.mul_le_mul_right m hq2) b1
  · have : (x / 2 ^ 192 * mu / 2 ^ 320 + 6) * m ≤ (q + 7) * m := Nat.mul_le_mul_right m (by omega)
    omega

/-- the final `while r ≥ m: r -= m` loop computes `r mod m` -/
theorem drain_mod (m : Nat) (hm : 0 < m) : ∀ (n r : Nat), r < n * m + m → ∃ k, r - k * m < m ∧ (r - k * m) = r % m := by
  intro n
  induction n with
  | zero => intro r hr; exact ⟨0, by simpa using hr, by simp; exact (Nat.mod_eq_of_lt (by simpa using hr)).symm⟩
  | succ n ih =>
    intro r hr
    by_cases h : r < m
    · exact ⟨0, by simpa using h, by simp; exact (Nat.mod_eq_of_lt h).symm⟩
    · have h' : r - m < n * m + m := by
        have : (n + 1) * m = n * m + m := by rw [Nat.add_mul, Nat.one_mul]
        omega
      obtain ⟨k, hk1, hk2⟩ := ih (r - m) h'
      refine ⟨k + 1, ?_, ?_⟩
      · have : (k + 1) * m = k * m + m := by rw [Nat.add_mul, Nat.one_mul]
        omega
      · have e : r % m = (r - m) % m := by
          have : r = (r - m) + m := by omega
          conv => lhs; rw [this]
          rw [Nat.add_mod_right]
        have : (k + 1) * m = k * m + m := by rw [Nat.add_mul, Nat.one_mul]
        omega

end Fv256.F
