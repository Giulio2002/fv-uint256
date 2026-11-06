import Fv256.SpecI
import Fv256.UtilI
import Fv256.DecCongr

/-! Pure lemmas for the top level of `SetFromDecimal` (arm64): the branch-free `s[1:]` pointer mask, etc. -/

namespace Fv256.TopMath

open Fv256.I Fv256.I.Fv256.I

theorem msb_neg (m : BitVec 64) (h0 : m ≠ 0#64) (h1 : m.toNat < 2 ^ 63) : (0#64 - m).getLsbD 63 = true := by
  have hm : 0 < m.toNat := by
    rcases Nat.eq_zero_or_pos m.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
    · exact h
  have : (0#64 - m).msb = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  simpa [BitVec.msb_eq_getLsbD_last] using this

theorem asr_and1 (m : BitVec 64) (hm : m.toNat < 2 ^ 63) :
    (((if (0#64 - m).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 |||
        (0#64 - m).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) &&& 1#64) =
      if m = 0#64 then 0#64 else 1#64 := by
  by_cases h0 : m = 0#64
  · subst h0; decide
  · rw [if_neg h0, if_pos (msb_neg m h0 hm)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_rotateRight]
    have key : ∀ j, j < 64 → ((18446744073709551615#64).getLsbD j && (18446744073709551614#64).getLsbD j) = decide (j ≠ 0) := by
      decide
    have k1 : ∀ j, j < 64 → (1#64).getLsbD j = decide (j = 0) := by decide
    rw [key i hi, k1 i hi]
    by_cases h5 : i = 0
    · subst h5
      have hb : (-m).getLsbD 63 = true := by simpa using msb_neg m h0 hm
      simp [hb]
    · simp [h5]

theorem plusEnd_le (b : Nat → Nat) (n : Nat) : plusEnd b n ≤ n := by
  unfold plusEnd; split <;> omega

theorem startPos_end (b : Nat → Nat) (n : Nat) (h : plusEnd b n = n) : startPos b n = n := by
  unfold startPos
  rw [h]
  simp [zerosFrom]

theorem startPos_nz (b : Nat → Nat) (n : Nat) (h : plusEnd b n < n) (hb : b (plusEnd b n) ≠ 48) :
    startPos b n = plusEnd b n := by
  obtain ⟨f, hf⟩ : ∃ f, n - plusEnd b n = f + 1 := ⟨n - plusEnd b n - 1, by omega⟩
  unfold startPos
  rw [hf]
  simp only [zerosFrom]
  simp [hb, h]
  intro h'; omega

theorem startPos_a (b : Nat → Nat) (n i : Nat) (h : plusEnd b n + i < n) (hb : b (plusEnd b n + i) ≠ 48)
    (hz : ∀ k, k < i → b (plusEnd b n + k) = 48) : startPos b n = plusEnd b n + i := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := startPos_spec b n
  have hl := startPos_lead b n (by omega)
  have hlt : plusEnd b n < n := by omega
  by_cases hc : startPos b n < plusEnd b n + i
  · have h48 : b (startPos b n) = 48 := by
      have := hz (startPos b n - plusEnd b n) (by omega)
      rw [show plusEnd b n + (startPos b n - plusEnd b n) = startPos b n by omega] at this
      exact this
    rcases hl with hl | hl
    · exact absurd h48 hl
    · omega
  · by_cases hd : startPos b n > plusEnd b n + i
    · have := s5 (plusEnd b n + i) (by omega) hd
      exact absurd this hb
    · omega

theorem startPos_b (b : Nat → Nat) (n : Nat) (h : plusEnd b n < n) (hz : ∀ k, plusEnd b n ≤ k → k < n → b k = 48) :
    startPos b n = n - 1 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := startPos_spec b n
  have hl := startPos_lead b n h
  have := s4 h
  rcases hl with hl | hl
  · exact absurd (hz _ s2 this) hl
  · exact hl

theorem allDec_shift (b : Nat → Nat) (p x y : Nat) : allDec b (p + x) (p + y) ↔ allDec (fun k => b (p + k)) x y := by
  unfold allDec
  constructor
  · intro h k h1 h2; exact h (p + k) (by omega) (by omega)
  · intro h k h1 h2
    have := h (k - p) (by omega) (by omega)
    simpa [show p + (k - p) = k by omega] using this

theorem firstBad_shift (b : Nat → Nat) (n p : Nat) (hp : p ≤ n) : ∀ f i,
    firstBad b n p f i = (firstBad (fun k => b (p + k)) (n - p) 0 f i).map (fun r => (p + r.1, r.2)) := by
  intro f
  induction f with
  | zero => intro i; simp [firstBad]
  | succ f ih =>
    intro i
    simp only [firstBad]
    by_cases h1 : n - p ≤ 19 * i
    · have h1' : n - p - 0 ≤ 19 * i := by omega
      simp [h1, h1']
    · have h1' : ¬ (n - p - 0 ≤ 19 * i) := by omega
      simp only [h1, h1', if_false]
      have e1 : (chunkBounds n p i).1 = p + (chunkBounds (n - p) 0 i).1 := by
        simp only [chunkBounds]; split <;> split <;> omega
      have e2 : (chunkBounds n p i).2 = p + (chunkBounds (n - p) 0 i).2 := by
        simp only [chunkBounds]; omega
      have e3 : allDec b (chunkBounds n p i).1 (chunkBounds n p i).2 ↔
          allDec (fun k => b (p + k)) (chunkBounds (n - p) 0 i).1 (chunkBounds (n - p) 0 i).2 := by
        rw [e1, e2]; exact allDec_shift b p _ _
      by_cases h2 : allDec b (chunkBounds n p i).1 (chunkBounds n p i).2
      · have h2' := e3.1 h2
        simp only [h2, h2', if_true]
        exact ih (i + 1)
      · have h2' : ¬ allDec (fun k => b (p + k)) (chunkBounds (n - p) 0 i).1 (chunkBounds (n - p) 0 i).2 := fun h => h2 (e3.2 h)
        simp only [h2, h2', if_false, Option.map_some]
        rw [e1, e2, Nat.add_sub_add_left]

/-- the result of `fromDec` on the stripped string, shifted back to absolute chunk positions -/
def shiftRes (p : Nat) : Res → Res
  | .syntax lo len => .syntax (p + lo) len
  | r => r

theorem fromDec_shift (b : Nat → Nat) (n p : Nat) (hp : p ≤ n) :
    fromDec b n p = shiftRes p (fromDec (fun k => b (p + k)) (n - p) 0) := by
  unfold fromDec
  by_cases h : n ≤ p
  · have h' : n - p ≤ 0 := by omega
    simp [h, h', shiftRes]
  · have h' : ¬ (n - p ≤ 0) := by omega
    simp only [h, h', if_false]
    rw [firstBad_shift b n p hp 5 0]
    cases hf : firstBad (fun k => b (p + k)) (n - p) 0 5 0 with
    | none =>
      simp only [Option.map_none, shiftRes]
      rw [Nat.sub_zero, decSum_off b p (n - p)]
    | some r =>
      simp [shiftRes]

theorem decParse_lt (b : Nat → Nat) (n : Nat) (h : n - startPos b n < 78) :
    decParse b n = fromDec b n (startPos b n) := by
  unfold decParse; simp [h]

theorem decParse_eq (b : Nat → Nat) (n : Nat) (h : n - startPos b n = 78)
    (hg : ¬ lexGt (fun k => b (startPos b n + k)) maxDigit 78) : decParse b n = fromDec b n (startPos b n) := by
  unfold decParse; simp [h, hg]

theorem decParse_gt78 (b : Nat → Nat) (n : Nat) (h : n - startPos b n = 78)
    (hg : lexGt (fun k => b (startPos b n + k)) maxDigit 78) : decParse b n = .range := by
  unfold decParse; simp [h, hg]

theorem decParse_big (b : Nat → Nat) (n : Nat) (h : 78 < n - startPos b n) : decParse b n = .range := by
  unfold decParse
  have h1 : ¬ (n - startPos b n < 78) := by omega
  have h2 : ¬ (n - startPos b n = 78) := by omega
  simp [h1, h2]

theorem startPos_spec' (b : Nat → Nat) (n : Nat) : startPos b n ≤ n := (startPos_spec b n).2.2.1

theorem dec_of_fd (b bs' : Nat → Nat) (n q len : Nat) (hq : q ≤ n) (hlen : len = n - q)
    (hb : ∀ j, j < len → bs' j = b (q + j)) (hdp : decParse b n = fromDec b n q) :
    decParse b n = shiftRes q (fromDec bs' len 0) := by
  rw [hdp, fromDec_shift b n q hq, hlen]
  congr 1
  exact Fv256.I.fromDec_congr _ _ (n - q) 0 (fun k hk => (hb k (by omega)).symm)

end Fv256.TopMath
