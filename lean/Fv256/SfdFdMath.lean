import Fv256.SpecI

/-!
# Arithmetic of the chunk loop of `fromDecimal`

The chunks of the digit string `b 0 .. b (n-1)` (`n ≤ 78`) are taken from the least significant end: round `i` covers
`[chunkLo, n - 19 i)` with `chunkLo = (chunkBounds n 0 i).1`.  After `i` rounds the accumulator holds
`decSum b (n - 19 i) (min n (19 i))`.
-/

namespace Fv256.I

/-- the value accumulated after `i` rounds -/
def accV (b : Nat → Nat) (n i : Nat) : Nat := decSum b (n - 19 * i) (min n (19 * i))

theorem accV_zero (b : Nat → Nat) (n : Nat) : accV b n 0 = 0 := by
  simp [accV, decSum]

theorem chunk_lo_le (n i : Nat) : (chunkBounds n 0 i).1 ≤ n - 19 * i := by
  unfold chunkBounds; dsimp only; split <;> omega

theorem chunk_hi (n i : Nat) : (chunkBounds n 0 i).2 = n - 19 * i := rfl

theorem chunk_lo_eq (n i : Nat) : (chunkBounds n 0 i).1 = n - 19 * (i + 1) := by
  unfold chunkBounds; dsimp only; split <;> omega

/-- one round adds the chunk times `10^(19 i)` -/
theorem accV_succ (b : Nat → Nat) (n i : Nat) (h : 19 * i < n) :
    accV b n (i + 1) = decSum b (n - 19 * (i + 1)) (n - 19 * i - (n - 19 * (i + 1))) * 10 ^ (19 * i) + accV b n i := by
  unfold accV
  have e1 : min n (19 * (i + 1)) = (n - 19 * i - (n - 19 * (i + 1))) + 19 * i := by omega
  have e2 : min n (19 * i) = 19 * i := by omega
  rw [e1, e2, decSum_add]
  have e3 : n - 19 * (i + 1) + (n - 19 * i - (n - 19 * (i + 1))) = n - 19 * i := by omega
  rw [e3]

theorem accV_lt (b : Nat → Nat) (n i : Nat) (hn : n ≤ 78) (hi : i ≤ 5) (hall : allDec b (n - 19 * i) n)
    (hfin : allDec b 0 n → decSum b 0 n < 2 ^ 256) : accV b n i < 2 ^ 256 := by
  unfold accV
  by_cases h4 : i ≤ 4
  · have h1 : decSum b (n - 19 * i) (min n (19 * i)) < 10 ^ (min n (19 * i)) := by
      apply decSum_lt
      intro k hk hk'
      exact hall k hk (by omega)
    have h2 : 10 ^ (min n (19 * i)) ≤ 10 ^ 76 := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : (10 : Nat) ^ 76 < 2 ^ 256 := by decide
    omega
  · have hi5 : i = 5 := by omega
    subst hi5
    have e1 : n - 19 * 5 = 0 := by omega
    have e2 : min n (19 * 5) = n := by omega
    rw [e1, e2]
    exact hfin (by rw [e1] at hall; exact hall)

theorem pow19_lt (i : Nat) (hi : i ≤ 4) : 10 ^ (19 * i) < 2 ^ 256 := by
  have h1 : 10 ^ (19 * i) ≤ 10 ^ 76 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (10 : Nat) ^ 76 < 2 ^ 256 := by decide
  omega

/-! ### `firstBad` -/

theorem fb_none_of_le (b : Nat → Nat) (n i : Nat) (hi : i < 5) (h : n ≤ 19 * i) : firstBad b n 0 (5 - i) i = none := by
  obtain ⟨f, hf⟩ : ∃ f, 5 - i = f + 1 := ⟨4 - i, by omega⟩
  rw [hf]
  simp only [firstBad]
  rw [if_pos (by omega)]

theorem fb_none_five (b : Nat → Nat) (n : Nat) : firstBad b n 0 (5 - 5) 5 = none := rfl

theorem fb_bad (b : Nat → Nat) (n i : Nat) (hi : i < 5) (h : 19 * i < n)
    (hb : ¬ allDec b (chunkBounds n 0 i).1 (chunkBounds n 0 i).2) :
    firstBad b n 0 (5 - i) i = some ((chunkBounds n 0 i).1, (chunkBounds n 0 i).2 - (chunkBounds n 0 i).1) := by
  obtain ⟨f, hf⟩ : ∃ f, 5 - i = f + 1 := ⟨4 - i, by omega⟩
  rw [hf]
  simp only [firstBad]
  rw [if_neg (by omega), if_neg hb]

theorem fb_good (b : Nat → Nat) (n i : Nat) (hi : i < 5) (h : 19 * i < n)
    (hb : allDec b (chunkBounds n 0 i).1 (chunkBounds n 0 i).2) :
    firstBad b n 0 (5 - i) i = firstBad b n 0 (5 - (i + 1)) (i + 1) := by
  obtain ⟨f, hf⟩ : ∃ f, 5 - i = f + 1 := ⟨4 - i, by omega⟩
  have hf' : 5 - (i + 1) = f := by omega
  rw [hf, hf']
  simp only [firstBad]
  rw [if_neg (by omega), if_pos hb]

/-- the 'ok' result of `fromDec` once no round is bad -/
theorem fromDec_ok_of_none (b : Nat → Nat) (n : Nat) (hn : 0 < n) (h : firstBad b n 0 5 0 = none) :
    fromDec b n 0 = .ok (decSum b 0 n) := by
  unfold fromDec
  rw [if_neg (by omega), h]
  simp

theorem fromDec_syntax_of_some (b : Nat → Nat) (n lo len : Nat) (hn : 0 < n) (h : firstBad b n 0 5 0 = some (lo, len)) :
    fromDec b n 0 = .syntax lo len := by
  unfold fromDec
  rw [if_neg (by omega), h]

theorem fromDec_eof (b : Nat → Nat) : fromDec b 0 0 = .eof := by
  unfold fromDec; simp

end Fv256.I

namespace Fv256.I

theorem allDec_join {b : Nat → Nat} {a c d : Nat} (h1 : allDec b a c) (h2 : allDec b c d) : allDec b a d := by
  intro k hk1 hk2
  by_cases h : k < c
  · exact h1 k hk1 h
  · exact h2 k (by omega) hk2

theorem allDec_mono {b : Nat → Nat} {a c a' c' : Nat} (h : allDec b a c) (h1 : a ≤ a') (h2 : c' ≤ c) : allDec b a' c' :=
  fun k hk1 hk2 => h k (by omega) (by omega)

/-- the bytes of a chunk, read at a shifted base, are the bytes of `b` -/
theorem chunk_allDec_iff (b : Nat → Nat) (c : Nat → Nat) (lo len : Nat) (hM : ∀ k, k < len → c k = b (lo + k)) :
    allDec c 0 len ↔ allDec b lo (lo + len) := by
  constructor
  · intro h k hk1 hk2
    have := h (k - lo) (by omega) (by omega)
    rw [hM (k - lo) (by omega)] at this
    have e : lo + (k - lo) = k := by omega
    rwa [e] at this
  · intro h k hk1 hk2
    rw [hM k hk2]
    exact h (lo + k) (by omega) (by omega)

theorem chunk_decSum (b : Nat → Nat) (c : Nat → Nat) (lo len : Nat) (hM : ∀ k, k < len → c k = b (lo + k)) :
    decSum c 0 len = decSum b lo len := by
  induction len with
  | zero => rfl
  | succ n ih =>
    have h1 : decSum c 0 (n + 1) = decSum c 0 n * 10 + (c (0 + n) - 48) := rfl
    have h2 : decSum b lo (n + 1) = decSum b lo n * 10 + (b (lo + n) - 48) := rfl
    rw [h1, h2, ih (fun k hk => hM k (by omega)), Nat.zero_add, hM n (by omega)]

end Fv256.I
