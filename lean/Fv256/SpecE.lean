
/-!
# Independent specification, family E (decimal / text / encoding)

Plain mathematical models, written without reference to the Go code or the machine.
-/

namespace Fv256.E

/-- The ASCII bytes of the base-10 representation of `n`, most significant digit first, without
leading zeros (`0` is `"0"`). -/
def decBytes (n : Nat) : List Nat :=
  if h : n < 10 then [48 + n] else decBytes (n / 10) ++ [48 + n % 10]
termination_by n
decreasing_by omega

/-- The number of decimal digits of `n` (`1` for `0`). -/
def decLen (n : Nat) : Nat := (decBytes n).length

theorem decBytes_lt (n : Nat) (h : n < 10) : decBytes n = [48 + n] := by
  rw [decBytes]; simp [h]

theorem decBytes_ge (n : Nat) (h : 10 ≤ n) : decBytes n = decBytes (n / 10) ++ [48 + n % 10] := by
  rw [decBytes]; simp; omega

theorem decLen_lt (n : Nat) (h : n < 10) : decLen n = 1 := by
  simp [decLen, decBytes_lt n h]

theorem decLen_ge (n : Nat) (h : 10 ≤ n) : decLen n = decLen (n / 10) + 1 := by
  simp [decLen, decBytes_ge n h]

theorem decLen_pos (n : Nat) : 1 ≤ decLen n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [decLen_lt n h]; omega
    · rw [decLen_ge n (by omega)]; omega

/-- `10^(decLen n - 1) ≤ n < 10^(decLen n)` (the first inequality for `n ≥ 1`, and `n = 0` has length 1). -/
theorem decLen_lt_pow (n : Nat) : n < 10 ^ decLen n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [decLen_lt n h]; omega
    · rw [decLen_ge n (by omega), Nat.pow_succ]
      have := ih (n / 10) (by omega)
      omega

theorem pow_decLen_le (n : Nat) (h : 1 ≤ n) : 10 ^ (decLen n - 1) ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n < 10
    · rw [decLen_lt n h1]; simp; omega
    · rw [decLen_ge n (by omega)]
      have := ih (n / 10) (by omega) (by omega)
      have hp : 10 ^ (decLen (n / 10) + 1 - 1) = 10 ^ (decLen (n/10) - 1) * 10 := by
        have := decLen_pos (n/10)
        rw [show decLen (n/10) + 1 - 1 = (decLen (n/10) - 1) + 1 by omega, Nat.pow_succ]
      rw [hp]; omega

theorem getD_append_left (a b : List Nat) (i : Nat) (h : i < a.length) : (a ++ b).getD i 0 = a.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- The byte at position `k` from the END of the decimal string of `n` (`k = 0` is the last digit)
is the digit `n / 10^k % 10`. -/
theorem decBytes_getD_rev (n : Nat) :
    ∀ k, k < decLen n → (decBytes n).getD (decLen n - 1 - k) 0 = 48 + n / 10 ^ k % 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    by_cases h : n < 10
    · have hk0 : k = 0 := by rw [decLen_lt n h] at hk; omega
      subst hk0
      rw [decLen_lt n h, decBytes_lt n h]
      simp; omega
    · have hl := decLen_ge n (by omega)
      have hb := decBytes_ge n (by omega)
      have hp := decLen_pos (n / 10)
      have hlen : (decBytes (n / 10)).length = decLen (n / 10) := rfl
      by_cases hk0 : k = 0
      · subst hk0
        rw [hl, hb]
        simp [List.getD_eq_getElem?_getD, hlen]
      · have hk1 : k - 1 < decLen (n / 10) := by omega
        have := ih (n / 10) (by omega) (k - 1) hk1
        rw [hl, hb]
        have hidx : decLen (n / 10) + 1 - 1 - k = decLen (n / 10) - 1 - (k - 1) := by omega
        rw [hidx, getD_append_left _ _ _ (by omega), this]
        have hpw : 10 ^ k = 10 ^ (k - 1) * 10 := by
          rw [← Nat.pow_succ]; congr 1; omega
        rw [hpw, Nat.div_div_eq_div_mul, Nat.mul_comm 10]

/-- Dividing by `10^k` removes `k` digits (when at least `10^k`). -/
theorem decLen_div_pow (u k : Nat) (h : 10 ^ k ≤ u) : decLen u = decLen (u / 10 ^ k) + k := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    have h1 : 10 ^ k ≤ u := Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h
    have h2 : 10 ≤ u / 10 ^ k := by
      rw [Nat.le_div_iff_mul_le (Nat.one_le_pow k 10 (by omega))]
      rw [Nat.pow_succ] at h; omega
    rw [ih u h1, decLen_ge _ h2, Nat.div_div_eq_div_mul, Nat.pow_succ]
    omega

/-- A number with `10^(d-1) ≤ u < 10^d` has `d` digits. -/
theorem decLen_of (u d : Nat) (hd : 1 ≤ d) (h1 : 10 ^ (d - 1) ≤ u) (h2 : u < 10 ^ d) : decLen u = d := by
  have a1 := decLen_lt_pow u
  have a2 := pow_decLen_le u (by have := Nat.one_le_pow (d - 1) 10 (by omega); omega)
  have b1 : decLen u - 1 < d := Nat.lt_of_not_le (fun hc => by
    have : 10 ^ d ≤ 10 ^ (decLen u - 1) := Nat.pow_le_pow_right (by omega) hc
    omega)
  have b2 : d - 1 < decLen u := Nat.lt_of_not_le (fun hc => by
    have : 10 ^ decLen u ≤ 10 ^ (d - 1) := Nat.pow_le_pow_right (by omega) hc
    omega)
  omega

/-- `decLen` of a 64-bit number is at most 20. -/
theorem decLen_le_20 (u : Nat) (hu : u < 2 ^ 64) : decLen u ≤ 20 := by
  by_cases h0 : u = 0
  · subst h0; simp [decLen, decBytes_lt 0 (by decide)]
  · have a2 := pow_decLen_le u (by omega)
    by_cases hc : decLen u ≤ 20
    · exact hc
    · have : 10 ^ 20 ≤ 10 ^ (decLen u - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h64 : 2 ^ 64 < 10 ^ 20 := by decide
      omega

end Fv256.E
