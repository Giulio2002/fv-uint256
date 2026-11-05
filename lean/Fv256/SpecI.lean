/-!
# Independent specification, family I (decimal parsers, RLP)

Plain mathematical models of `SetFromDecimal` (and its wrappers) and of the Ethereum RLP encoding of a
256-bit integer, written from the documentation, without reference to the compiled code:

* `SetFromDecimal` doc (master 48f3f44): "sets z from the given string, interpreted as a decimal number ...
  does not accept underscore input, does not accept negative zero or any negative input"; `FromDecimal` doc:
  "Numbers larger than 256 bits are not accepted".  The accepted syntax is: at most one leading `+`, then any
  number of ASCII digits `0`-`9` (leading zeros are fine, no other character, at least one digit), whose value is
  `< 2^256`.  Everything else is an error.
* Errors: the empty digit string is `io.EOF`; a digit string with value `>= 2^256` is `ErrBig256Range`; a
  non-digit is a `*strconv.NumError{Func: "ParseUint", Num: <the failing chunk>, Err: ErrSyntax}` (the digits are
  parsed in chunks of 19 characters, least significant first).  The documentation does not say which error wins
  when a string is both too long and malformed; `DecRes` records what the library does (`decParse`) and the
  theorems `decParse_ok_iff`, `decParse_range_of_valid`, `decParse_eof_iff` show that the accepted language and the
  classification of well-formed input are exactly the documented ones.
-/

namespace Fv256.I

/-- ASCII decimal digit. -/
def isDec (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

/-- positional value (base 10, most significant first) of the `n` bytes `b a, ..., b (a+n-1)` (a non-digit counts `0`). -/
def decSum (b : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => decSum b a n * 10 + (b (a + n) - 48)

/-- every byte of `[a, c)` is an ASCII digit. -/
def allDec (b : Nat → Nat) (a c : Nat) : Prop := ∀ k, a ≤ k → k < c → isDec (b k)

theorem decSum_add (b : Nat → Nat) (a m : Nat) : ∀ n, decSum b a (m + n) = decSum b a m * 10 ^ n + decSum b (a + m) n
  | 0 => by simp [decSum]
  | n + 1 => by
    have ih := decSum_add b a m n
    have h1 : decSum b a (m + (n + 1)) = decSum b a (m + n) * 10 + (b (a + (m + n)) - 48) := rfl
    have h2 : decSum b (a + m) (n + 1) = decSum b (a + m) n * 10 + (b (a + m + n) - 48) := rfl
    rw [h1, ih, h2, Nat.pow_succ]
    have e1 : a + (m + n) = a + m + n := by omega
    have e2 : decSum b a m * (10 ^ n * 10) = decSum b a m * 10 ^ n * 10 := by rw [Nat.mul_assoc]
    rw [e1, Nat.add_mul, e2]
    omega

theorem decSum_zero (b : Nat → Nat) (a : Nat) : ∀ n, (∀ k, a ≤ k → k < a + n → b k = 48) → decSum b a n = 0
  | 0, _ => rfl
  | n + 1, h => by
    have h1 : decSum b a (n + 1) = decSum b a n * 10 + (b (a + n) - 48) := rfl
    rw [h1, decSum_zero b a n (fun k hk hk' => h k hk (by omega)), h (a + n) (by omega) (by omega)]

theorem decSum_congr (b b' : Nat → Nat) (a : Nat) : ∀ n, (∀ k, a ≤ k → k < a + n → b k = b' k) → decSum b a n = decSum b' a n
  | 0, _ => rfl
  | n + 1, h => by
    have h1 : decSum b a (n + 1) = decSum b a n * 10 + (b (a + n) - 48) := rfl
    have h2 : decSum b' a (n + 1) = decSum b' a n * 10 + (b' (a + n) - 48) := rfl
    rw [h1, h2, decSum_congr b b' a n (fun k hk hk' => h k hk (by omega)), h (a + n) (by omega) (by omega)]

theorem decSum_lt (b : Nat → Nat) (a : Nat) : ∀ n, allDec b a (a + n) → decSum b a n < 10 ^ n
  | 0, _ => by simp [decSum]
  | n + 1, h => by
    have h1 : decSum b a (n + 1) = decSum b a n * 10 + (b (a + n) - 48) := rfl
    have ih := decSum_lt b a n (fun k hk hk' => h k hk (by omega))
    have hd := h (a + n) (by omega) (by omega)
    unfold isDec at hd
    rw [h1, Nat.pow_succ]
    omega

/-! ## Syntax and classification -/

/-- the offset after at most one leading `+`. -/
def plusEnd (b : Nat → Nat) (n : Nat) : Nat := if 0 < n ∧ b 0 = 43 then 1 else 0

/-- the number of consecutive `'0'` bytes of `b` starting at `a`, below `n` (fuel `f`). -/
def zerosFrom (b : Nat → Nat) (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, a => if a < n ∧ b a = 48 then zerosFrom b n f (a + 1) + 1 else 0

/-- the start of the number after the leading `+` and the leading zeros are dropped; an all-zero string keeps one
`'0'` (so that `"000"` parses as `0`, not as the empty string). -/
def startPos (b : Nat → Nat) (n : Nat) : Nat :=
  if plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n) = n ∧ plusEnd b n < n then n - 1
  else plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n)

/-- the 19-character chunk of round `i` (counted from the least significant end `n`) of the number starting at `p`:
`[lo, hi)`. -/
def chunkBounds (n p i : Nat) : Nat × Nat :=
  (if p + 19 ≤ n - 19 * i then n - 19 * i - 19 else p, n - 19 * i)

open Classical in
/-- the first (least significant) chunk that has a non-digit, as `(lo, len)`. -/
noncomputable def firstBad (b : Nat → Nat) (n p : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | f + 1, i =>
    if n - p ≤ 19 * i then none
    else if allDec b (chunkBounds n p i).1 (chunkBounds n p i).2 then firstBad b n p f (i + 1)
    else some ((chunkBounds n p i).1, (chunkBounds n p i).2 - (chunkBounds n p i).1)

/-- the outcome of `SetFromDecimal`: the number, `io.EOF`, `ErrBig256Range`, or the `strconv` syntax error of the
chunk `[lo, lo+len)` of the original string. -/
inductive Res
  | ok (v : Nat)
  | eof
  | range
  | syntax (lo len : Nat)
  deriving DecidableEq

open Classical in
/-- parse the stripped digit string `[p, n)` (at most 78 digits). -/
noncomputable def fromDec (b : Nat → Nat) (n p : Nat) : Res :=
  if n ≤ p then .eof
  else match firstBad b n p 5 0 with
    | some (lo, len) => .syntax lo len
    | none => .ok (decSum b p (n - p))

/-- the decimal digits of `2^256 - 1` (78 of them), as ASCII codes. -/
def maxDigit (k : Nat) : Nat := (2 ^ 256 - 1) / 10 ^ (77 - k) % 10 + 48

/-- bytewise lexicographic `x > y` on the first `n` bytes. -/
def lexGt (x y : Nat → Nat) (n : Nat) : Prop := ∃ k, k < n ∧ (∀ j, j < k → x j = y j) ∧ y k < x k

open Classical in
/-- `SetFromDecimal(s)` for the string whose bytes are `b 0, ..., b (n-1)`. -/
noncomputable def decParse (b : Nat → Nat) (n : Nat) : Res :=
  if n - startPos b n < 78 then fromDec b n (startPos b n)
  else if n - startPos b n = 78 then
    (if lexGt (fun k => b (startPos b n + k)) maxDigit 78 then .range else fromDec b n (startPos b n))
  else .range

namespace Fv256.I

theorem maxDigit_isDec : ∀ k, k < 78 → isDec (maxDigit k) := by
  intro k hk
  unfold isDec maxDigit
  have := Nat.mod_lt ((2 ^ 256 - 1) / 10 ^ (77 - k)) (by decide : 10 > 0)
  omega

set_option maxRecDepth 100000 in
theorem decSum_maxDigit : decSum maxDigit 0 78 = 2 ^ 256 - 1 := by decide +kernel

theorem decSum_shift (z : Nat → Nat) (a : Nat) : ∀ n, decSum (fun j => z (j + 1)) a n = decSum z (a + 1) n
  | 0 => rfl
  | n + 1 => by
    have a1 : decSum (fun j => z (j + 1)) a (n + 1) = decSum (fun j => z (j + 1)) a n * 10 + (z (a + n + 1) - 48) := rfl
    have a2 : decSum z (a + 1) (n + 1) = decSum z (a + 1) n * 10 + (z (a + 1 + n) - 48) := rfl
    rw [a1, a2, decSum_shift z a n, show a + n + 1 = a + 1 + n by omega]

/-- on equal-length digit strings, bytewise lexicographic order is numeric order -/
theorem lexGt_iff : ∀ (n : Nat) (x y : Nat → Nat), allDec x 0 n → allDec y 0 n →
    (lexGt x y n ↔ decSum y 0 n < decSum x 0 n)
  | 0, x, y, _, _ => by simp [lexGt, decSum]
  | n + 1, x, y, hx, hy => by
    have ex' : ∀ z : Nat → Nat, decSum z 0 (n + 1) = (z 0 - 48) * 10 ^ n + decSum z 1 n := by
      intro z
      have := decSum_add z 0 1 n
      rw [Nat.add_comm n 1, this]
      simp [decSum]
    have hx0 := hx 0 (Nat.le_refl 0) (by omega)
    have hy0 := hy 0 (Nat.le_refl 0) (by omega)
    unfold isDec at hx0 hy0
    have hxl : decSum x 1 n < 10 ^ n := decSum_lt x 1 n (fun k hk hk' => hx k (by omega) (by omega))
    have hyl : decSum y 1 n < 10 ^ n := decSum_lt y 1 n (fun k hk hk' => hy k (by omega) (by omega))
    have ih := lexGt_iff n (fun j => x (j + 1)) (fun j => y (j + 1))
      (fun k hk hk' => hx (k + 1) (by omega) (by omega)) (fun k hk hk' => hy (k + 1) (by omega) (by omega))
    rw [decSum_shift x 0 n, decSum_shift y 0 n] at ih
    simp only [Nat.zero_add] at ih
    rw [ex' x, ex' y]
    constructor
    · rintro ⟨k, hk, hpre, hlt⟩
      rcases Nat.eq_zero_or_pos k with rfl | hkp
      · have : (y 0 - 48) * 10 ^ n + decSum y 1 n < (x 0 - 48) * 10 ^ n + decSum x 1 n := by
          have h1 : (y 0 - 48 + 1) * 10 ^ n ≤ (x 0 - 48) * 10 ^ n :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul] at h1
          omega
        exact this
      · have h0 : x 0 = y 0 := hpre 0 hkp
        have : lexGt (fun j => x (j + 1)) (fun j => y (j + 1)) n := by
          refine ⟨k - 1, by omega, fun j hj => ?_, ?_⟩
          · have := hpre (j + 1) (by omega); exact this
          · have := hlt; simpa [show k - 1 + 1 = k by omega] using this
        have := ih.mp this
        rw [h0]; omega
    · intro h
      by_cases h0 : x 0 = y 0
      · rw [h0] at h
        have h' : decSum y 1 n < decSum x 1 n := by omega
        obtain ⟨k, hk, hpre, hlt⟩ := ih.mpr h'
        refine ⟨k + 1, by omega, fun j hj => ?_, hlt⟩
        rcases Nat.eq_zero_or_pos j with rfl | hjp
        · exact h0
        · have := hpre (j - 1) (by omega)
          simpa [show j - 1 + 1 = j by omega] using this
      · have hlt0 : y 0 < x 0 := by
          apply Nat.lt_of_not_ge
          intro hc
          have : x 0 < y 0 := by omega
          have h1 : (x 0 - 48 + 1) * 10 ^ n ≤ (y 0 - 48) * 10 ^ n :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul] at h1
          omega
        exact ⟨0, by omega, fun j hj => by omega, hlt0⟩

theorem zerosFrom_spec (b : Nat → Nat) (n : Nat) : ∀ f a, a ≤ n → n - a ≤ f →
    a + zerosFrom b n f a ≤ n ∧ (∀ k, a ≤ k → k < a + zerosFrom b n f a → b k = 48) ∧
      (a + zerosFrom b n f a = n ∨ b (a + zerosFrom b n f a) ≠ 48)
  | 0, a, ha, hf => by
    simp only [zerosFrom]
    have : a = n := by omega
    exact ⟨by omega, fun k hk hk' => by omega, Or.inl (by omega)⟩
  | f + 1, a, ha, hf => by
    simp only [zerosFrom]
    by_cases hc : a < n ∧ b a = 48
    · rw [if_pos hc]
      obtain ⟨h1, h2, h3⟩ := zerosFrom_spec b n f (a + 1) (by omega) (by omega)
      have e : a + (zerosFrom b n f (a + 1) + 1) = a + 1 + zerosFrom b n f (a + 1) := by omega
      rw [e]
      refine ⟨by omega, fun k hk hk' => ?_, h3⟩
      by_cases hka : k = a
      · subst hka; exact hc.2
      · exact h2 k (by omega) (by omega)
    · rw [if_neg hc]
      refine ⟨by omega, fun k hk hk' => by omega, ?_⟩
      simp only [Nat.add_zero]
      rcases Classical.not_and_iff_not_or_not.mp hc with h | h
      · omega
      · exact Or.inr h

theorem startPos_spec (b : Nat → Nat) (n : Nat) :
    plusEnd b n ≤ n ∧ plusEnd b n ≤ startPos b n ∧ startPos b n ≤ n ∧
      (plusEnd b n < n → startPos b n < n) ∧
      (∀ k, plusEnd b n ≤ k → k < startPos b n → b k = 48) := by
  have hp : plusEnd b n ≤ n := by unfold plusEnd; split <;> omega
  obtain ⟨h1, h2, h3⟩ := zerosFrom_spec b n (n - plusEnd b n) (plusEnd b n) hp (Nat.le_refl _)
  unfold startPos
  split
  · rename_i hc
    refine ⟨hp, by omega, by omega, fun _ => by omega, fun k hk hk' => ?_⟩
    exact h2 k hk (by omega)
  · rename_i hc
    refine ⟨hp, by omega, by omega, fun hlt => ?_, fun k hk hk' => h2 k hk hk'⟩
    rcases Classical.not_and_iff_not_or_not.mp hc with h | h <;> omega

theorem allDec_mono {b : Nat → Nat} {a a' c : Nat} (h : allDec b a c) (h1 : a ≤ a') : allDec b a' c :=
  fun k hk hk' => h k (by omega) hk'

theorem allDec_join {b : Nat → Nat} {a c d : Nat} (h1 : allDec b a c) (h2 : allDec b c d) : allDec b a d := by
  intro k hk hk'
  by_cases h : k < c
  · exact h1 k hk h
  · exact h2 k (by omega) hk'

/-- the chunk scan finds no bad chunk exactly when the whole number is made of digits -/
theorem firstBad_none_iff (b : Nat → Nat) (n p : Nat) : ∀ f i, n - p ≤ 19 * (i + f) →
    (firstBad b n p f i = none ↔ allDec b p (n - 19 * i))
  | 0, i, hf => by
    simp only [firstBad, true_iff]
    intro k hk hk'; omega
  | f + 1, i, hf => by
    simp only [firstBad]
    by_cases h0 : n - p ≤ 19 * i
    · rw [if_pos h0]
      simp only [true_iff]
      intro k hk hk'; omega
    · rw [if_neg h0]
      by_cases hc : allDec b (chunkBounds n p i).1 (chunkBounds n p i).2
      · rw [if_pos hc]
        have ih := firstBad_none_iff b n p f (i + 1) (by omega)
        rw [ih]
        have hb : (chunkBounds n p i).2 = n - 19 * i := rfl
        constructor
        · intro hr
          by_cases hcase : p + 19 ≤ n - 19 * i
          · have hl : (chunkBounds n p i).1 = n - 19 * i - 19 := by simp [chunkBounds, hcase]
            rw [hl, hb] at hc
            have : n - 19 * (i + 1) = n - 19 * i - 19 := by omega
            rw [this] at hr
            exact allDec_join hr hc
          · have hl : (chunkBounds n p i).1 = p := by simp [chunkBounds, hcase]
            rw [hl, hb] at hc
            exact hc
        · intro h
          intro k hk hk'
          exact h k hk (by omega)
      · rw [if_neg hc]
        simp only [reduceCtorEq, false_iff]
        intro hall
        apply hc
        have hb : (chunkBounds n p i).2 = n - 19 * i := rfl
        have hl : p ≤ (chunkBounds n p i).1 := by
          unfold chunkBounds; simp only; split <;> omega
        intro k hk hk'
        exact hall k (by omega) (by omega)

theorem decSum_off (b : Nat → Nat) (p : Nat) : ∀ n, decSum (fun k => b (p + k)) 0 n = decSum b p n
  | 0 => rfl
  | n + 1 => by
    have a1 : decSum (fun k => b (p + k)) 0 (n + 1) = decSum (fun k => b (p + k)) 0 n * 10 + (b (p + (0 + n)) - 48) := rfl
    have a2 : decSum b p (n + 1) = decSum b p n * 10 + (b (p + n) - 48) := rfl
    rw [a1, a2, decSum_off b p n, Nat.zero_add]

theorem decSum_ge (b : Nat → Nat) (a n : Nat) : decSum b a (n + 1) ≥ (b a - 48) * 10 ^ n := by
  have := decSum_add b a 1 n
  rw [Nat.add_comm n 1, this]
  have : decSum b a 1 = b a - 48 := by simp [decSum]
  rw [this]
  omega

theorem startPos_lead (b : Nat → Nat) (n : Nat) (h : plusEnd b n < n) :
    b (startPos b n) ≠ 48 ∨ startPos b n = n - 1 := by
  have hp : plusEnd b n ≤ n := by unfold plusEnd; split <;> omega
  obtain ⟨h1, h2, h3⟩ := zerosFrom_spec b n (n - plusEnd b n) (plusEnd b n) hp (Nat.le_refl _)
  unfold startPos
  split
  · exact Or.inr rfl
  · rename_i hc
    left
    rcases h3 with h3 | h3
    · exact absurd ⟨h3, h⟩ hc
    · exact h3

theorem pow77_lt : 10 ^ 77 < 2 ^ 256 := by decide +kernel
theorem pow78_gt : 2 ^ 256 ≤ 10 ^ 78 := by decide +kernel

/-- `SetFromDecimal` accepts exactly: at most one `+`, at least one digit, only digits, value `< 2^256`. -/
theorem decParse_ok_iff (b : Nat → Nat) (n v : Nat) :
    decParse b n = .ok v ↔
      plusEnd b n < n ∧ allDec b (plusEnd b n) n ∧ v = decSum b (plusEnd b n) (n - plusEnd b n) ∧ v < 2 ^ 256 := by
  obtain ⟨sp0, sp1, sp2, sp3, sp4⟩ := startPos_spec b n
  have hp0 : plusEnd b n ≤ n := sp0
  -- the stripped number is the number
  have hval : plusEnd b n < n → decSum b (plusEnd b n) (n - plusEnd b n) = decSum b (startPos b n) (n - startPos b n) := by
    intro hlt
    have hh := decSum_add b (plusEnd b n) (startPos b n - plusEnd b n) (n - startPos b n)
    rw [show startPos b n - plusEnd b n + (n - startPos b n) = n - plusEnd b n by omega,
      show plusEnd b n + (startPos b n - plusEnd b n) = startPos b n by omega] at hh
    rw [hh, decSum_zero b (plusEnd b n) (startPos b n - plusEnd b n)
      (fun k hk hk' => sp4 k hk (by omega))]
    simp
  have hall : plusEnd b n < n → (allDec b (plusEnd b n) n ↔ allDec b (startPos b n) n) := by
    intro hlt
    constructor
    · intro h; exact allDec_mono h sp1
    · intro h
      refine allDec_join (c := startPos b n) (fun k hk hk' => ?_) h
      rw [sp4 k hk hk']; unfold isDec; omega
  unfold decParse
  constructor
  · intro hok
    have hlt : plusEnd b n < n := by
      refine Classical.byContradiction fun hc => ?_
      have h1 : startPos b n = n := by omega
      have : n - startPos b n < 78 := by omega
      rw [if_pos this] at hok
      unfold fromDec at hok
      simp [h1] at hok
    have hsl : startPos b n < n := sp3 hlt
    -- common: fromDec ok v
    have hfd : fromDec b n (startPos b n) = .ok v →
        allDec b (startPos b n) n ∧ v = decSum b (startPos b n) (n - startPos b n) := by
      intro hf
      unfold fromDec at hf
      rw [if_neg (by omega)] at hf
      cases hfb : firstBad b n (startPos b n) 5 0 with
      | some r => rw [hfb] at hf; obtain ⟨lo, len⟩ := r; simp at hf
      | none =>
        rw [hfb] at hf
        simp only [Res.ok.injEq] at hf
        have := (firstBad_none_iff b n (startPos b n) 5 0 (by
          by_cases h78 : n - startPos b n < 78
          · omega
          · rw [if_neg h78] at hok
            split at hok
            · split at hok
              · simp at hok
              · omega
            · simp at hok)).mp hfb
        simp only [Nat.mul_zero, Nat.sub_zero] at this
        exact ⟨this, hf.symm⟩
    by_cases h78 : n - startPos b n < 78
    · rw [if_pos h78] at hok
      obtain ⟨ha, hv⟩ := hfd hok
      refine ⟨hlt, (hall hlt).mpr ha, by rw [hval hlt]; exact hv, ?_⟩
      have := decSum_lt b (startPos b n) (n - startPos b n) (by rw [Nat.add_sub_cancel' (by omega)]; exact ha)
      have h10 : 10 ^ (n - startPos b n) ≤ 10 ^ 77 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [hv]; have := pow77_lt; omega
    · rw [if_neg h78] at hok
      by_cases h78' : n - startPos b n = 78
      · rw [if_pos h78'] at hok
        by_cases hlex : lexGt (fun k => b (startPos b n + k)) maxDigit 78
        · rw [if_pos hlex] at hok; simp at hok
        · rw [if_neg hlex] at hok
          obtain ⟨ha, hv⟩ := hfd hok
          refine ⟨hlt, (hall hlt).mpr ha, by rw [hval hlt]; exact hv, ?_⟩
          have hdx : allDec (fun k => b (startPos b n + k)) 0 78 := fun k _ hk' => ha _ (by omega) (by omega)
          have hdy : allDec maxDigit 0 78 := fun k _ hk' => maxDigit_isDec k hk'
          have := mt (lexGt_iff 78 _ _ hdx hdy).mpr hlex
          rw [decSum_off, decSum_maxDigit] at this
          rw [hv, h78'] ; omega
      · rw [if_neg h78'] at hok; simp at hok
  · rintro ⟨hlt, hdig, hv, hlt2⟩
    have hsl : startPos b n < n := sp3 hlt
    have hdig' : allDec b (startPos b n) n := (hall hlt).mp hdig
    have hv' : v = decSum b (startPos b n) (n - startPos b n) := by rw [hv, hval hlt]
    have hfb : firstBad b n (startPos b n) 5 0 = none := by
      have hL : n - startPos b n ≤ 78 := by
        refine Classical.byContradiction fun hc => ?_
        have hc' : n - startPos b n ≥ 79 := by omega
        rcases startPos_lead b n hlt with hne | heq
        · have hd := hdig' (startPos b n) (Nat.le_refl _) hsl
          unfold isDec at hd
          have hge := decSum_ge b (startPos b n) (n - startPos b n - 1)
          rw [Nat.sub_add_cancel (by omega)] at hge
          have h1 : (b (startPos b n) - 48) ≥ 1 := by omega
          have h2 : 10 ^ (n - startPos b n - 1) ≥ 10 ^ 78 := Nat.pow_le_pow_right (by decide) (by omega)
          have h3 := Nat.mul_le_mul h1 h2
          have := pow78_gt
          omega
        · omega
      exact (firstBad_none_iff b n (startPos b n) 5 0 (by omega)).mpr (by simpa using hdig')
    by_cases h78 : n - startPos b n < 78
    · rw [if_pos h78]
      unfold fromDec
      rw [if_neg (by omega), hfb]
      simp [hv']
    · have h78' : n - startPos b n = 78 := by
        refine Classical.byContradiction fun hc => ?_
        rcases startPos_lead b n hlt with hne | heq
        · have hd := hdig' (startPos b n) (Nat.le_refl _) hsl
          unfold isDec at hd
          have hge := decSum_ge b (startPos b n) (n - startPos b n - 1)
          rw [Nat.sub_add_cancel (by omega)] at hge
          have h1 : (b (startPos b n) - 48) ≥ 1 := by omega
          have h2 : 10 ^ (n - startPos b n - 1) ≥ 10 ^ 78 := Nat.pow_le_pow_right (by decide) (by omega)
          have h3 := Nat.mul_le_mul h1 h2
          have := pow78_gt
          omega
        · omega
      rw [if_neg h78, if_pos h78']
      have hdx : allDec (fun k => b (startPos b n + k)) 0 78 := fun k _ hk' => hdig' _ (by omega) (by omega)
      have hdy : allDec maxDigit 0 78 := fun k _ hk' => maxDigit_isDec k hk'
      have hnl : ¬ lexGt (fun k => b (startPos b n + k)) maxDigit 78 := by
        intro hl
        have := (lexGt_iff 78 _ _ hdx hdy).mp hl
        rw [decSum_off, decSum_maxDigit, ← h78', ← hv'] at this
        omega
      rw [if_neg hnl]
      unfold fromDec
      rw [if_neg (by omega), hfb]
      simp [hv']

theorem decParse_eof_iff (b : Nat → Nat) (n : Nat) : decParse b n = .eof ↔ plusEnd b n = n := by
  obtain ⟨sp0, sp1, sp2, sp3, sp4⟩ := startPos_spec b n
  unfold decParse
  constructor
  · intro h
    refine Classical.byContradiction fun hc => ?_
    have hlt : plusEnd b n < n := by omega
    have hsl := sp3 hlt
    by_cases h78 : n - startPos b n < 78
    · rw [if_pos h78] at h
      unfold fromDec at h
      rw [if_neg (by omega)] at h
      cases hfb : firstBad b n (startPos b n) 5 0 with
      | some r => rw [hfb] at h; obtain ⟨lo, len⟩ := r; simp at h
      | none => rw [hfb] at h; simp at h
    · rw [if_neg h78] at h
      by_cases h78' : n - startPos b n = 78
      · rw [if_pos h78'] at h
        split at h
        · simp at h
        · unfold fromDec at h
          rw [if_neg (by omega)] at h
          cases hfb : firstBad b n (startPos b n) 5 0 with
          | some r => rw [hfb] at h; obtain ⟨lo, len⟩ := r; simp at h
          | none => rw [hfb] at h; simp at h
      · rw [if_neg h78'] at h; simp at h
  · intro h
    have h1 : startPos b n = n := by omega
    rw [if_pos (by omega)]
    unfold fromDec
    rw [if_pos (by omega)]

theorem value_strip (b : Nat → Nat) (n : Nat) (hlt : plusEnd b n < n) :
    decSum b (plusEnd b n) (n - plusEnd b n) = decSum b (startPos b n) (n - startPos b n) := by
  obtain ⟨sp0, sp1, sp2, sp3, sp4⟩ := startPos_spec b n
  have hh := decSum_add b (plusEnd b n) (startPos b n - plusEnd b n) (n - startPos b n)
  rw [show startPos b n - plusEnd b n + (n - startPos b n) = n - plusEnd b n by omega,
    show plusEnd b n + (startPos b n - plusEnd b n) = startPos b n by omega] at hh
  rw [hh, decSum_zero b (plusEnd b n) (startPos b n - plusEnd b n)
    (fun k hk hk' => sp4 k hk (by omega))]
  simp

/-- a well-formed number too large for 256 bits is `ErrBig256Range`. -/
theorem decParse_range_of_valid (b : Nat → Nat) (n : Nat) (hlt : plusEnd b n < n) (hd : allDec b (plusEnd b n) n)
    (hv : 2 ^ 256 ≤ decSum b (plusEnd b n) (n - plusEnd b n)) : decParse b n = .range := by
  obtain ⟨sp0, sp1, sp2, sp3, sp4⟩ := startPos_spec b n
  have hsl := sp3 hlt
  have hdig : allDec b (startPos b n) n := allDec_mono hd sp1
  have hv' := value_strip b n hlt
  rw [hv'] at hv
  unfold decParse
  by_cases h78 : n - startPos b n < 78
  · exfalso
    have := decSum_lt b (startPos b n) (n - startPos b n) (by rw [Nat.add_sub_cancel' (by omega)]; exact hdig)
    have h10 : 10 ^ (n - startPos b n) ≤ 10 ^ 77 := Nat.pow_le_pow_right (by decide) (by omega)
    have := pow77_lt
    omega
  · rw [if_neg h78]
    by_cases h78' : n - startPos b n = 78
    · rw [if_pos h78']
      have hdx : allDec (fun k => b (startPos b n + k)) 0 78 := fun k _ hk' => hdig _ (by omega) (by omega)
      have hdy : allDec maxDigit 0 78 := fun k _ hk' => maxDigit_isDec k hk'
      have hl : lexGt (fun k => b (startPos b n + k)) maxDigit 78 := by
        refine (lexGt_iff 78 _ _ hdx hdy).mpr ?_
        rw [decSum_off, decSum_maxDigit, ← h78']
        omega
      rw [if_pos hl]
    · rw [if_neg h78']

theorem firstBad_some (b : Nat → Nat) (n p : Nat) : ∀ f i lo len, firstBad b n p f i = some (lo, len) →
    p ≤ lo ∧ 0 < len ∧ lo + len ≤ n ∧ ¬ allDec b lo (lo + len)
  | 0, i, lo, len, h => by simp [firstBad] at h
  | f + 1, i, lo, len, h => by
    simp only [firstBad] at h
    by_cases h0 : n - p ≤ 19 * i
    · rw [if_pos h0] at h; simp at h
    · rw [if_neg h0] at h
      by_cases hc : allDec b (chunkBounds n p i).1 (chunkBounds n p i).2
      · rw [if_pos hc] at h
        exact firstBad_some b n p f (i + 1) lo len h
      · rw [if_neg hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        have hb : (chunkBounds n p i).2 = n - 19 * i := rfl
        have hl : p ≤ (chunkBounds n p i).1 := by
          unfold chunkBounds; simp only; split <;> omega
        have hl2 : (chunkBounds n p i).1 < (chunkBounds n p i).2 := by
          unfold chunkBounds; simp only; split <;> omega
        have hl3 : (chunkBounds n p i).2 ≤ n := by rw [hb]; omega
        refine ⟨hl, by omega, by omega, ?_⟩
        rw [show (chunkBounds n p i).1 + len = (chunkBounds n p i).2 by omega]
        exact hc

/-- a syntax error names a non-empty chunk of the input that contains a non-digit. -/
theorem decParse_syntax (b : Nat → Nat) (n lo len : Nat) (h : decParse b n = .syntax lo len) :
    0 < len ∧ lo + len ≤ n ∧ ¬ allDec b lo (lo + len) := by
  unfold decParse at h
  have key : fromDec b n (startPos b n) = .syntax lo len → 0 < len ∧ lo + len ≤ n ∧ ¬ allDec b lo (lo + len) := by
    intro hf
    unfold fromDec at hf
    split at hf
    · simp at hf
    · cases hfb : firstBad b n (startPos b n) 5 0 with
      | some r =>
        obtain ⟨lo', len'⟩ := r
        rw [hfb] at hf
        simp only [Res.syntax.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        obtain ⟨-, h2, h3, h4⟩ := firstBad_some b n _ 5 0 _ _ hfb
        exact ⟨h2, h3, h4⟩
      | none => rw [hfb] at hf; simp at hf
  by_cases h78 : n - startPos b n < 78
  · rw [if_pos h78] at h; exact key h
  · rw [if_neg h78] at h
    by_cases h78' : n - startPos b n = 78
    · rw [if_pos h78'] at h
      split at h
      · simp at h
      · exact key h
    · rw [if_neg h78'] at h; simp at h

end Fv256.I
