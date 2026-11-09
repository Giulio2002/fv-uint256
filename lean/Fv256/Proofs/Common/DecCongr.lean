import Fv256.Proofs.Common.SpecI

/-! `decParse` reads only the bytes `b 0 .. b (n-1)`. -/

namespace Fv256.I

theorem plusEnd_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) : plusEnd b n = plusEnd b' n := by
  unfold plusEnd
  by_cases h0 : 0 < n
  · rw [h 0 h0]
  · simp [h0]

theorem zerosFrom_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) :
    ∀ f a, zerosFrom b n f a = zerosFrom b' n f a := by
  intro f
  induction f with
  | zero => intro a; rfl
  | succ f ih =>
    intro a
    simp only [zerosFrom]
    by_cases ha : a < n
    · rw [h a ha, ih (a + 1)]
    · simp [ha]

theorem startPos_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) : startPos b n = startPos b' n := by
  unfold startPos
  rw [plusEnd_congr b b' n h, zerosFrom_congr b b' n h]

theorem allDec_congr (b b' : Nat → Nat) (a c n : Nat) (hc : c ≤ n) (h : ∀ k, k < n → b k = b' k) :
    allDec b a c ↔ allDec b' a c := by
  unfold allDec
  constructor
  · intro H k h1 h2; rw [← h k (by omega)]; exact H k h1 h2
  · intro H k h1 h2; rw [h k (by omega)]; exact H k h1 h2

theorem firstBad_congr (b b' : Nat → Nat) (n p : Nat) (hp : p ≤ n) (h : ∀ k, k < n → b k = b' k) :
    ∀ f i, firstBad b n p f i = firstBad b' n p f i := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
    intro i
    simp only [firstBad]
    by_cases h1 : n - p ≤ 19 * i
    · simp [h1]
    · have hc : (chunkBounds n p i).2 ≤ n := by simp only [chunkBounds]; omega
      have := allDec_congr b b' (chunkBounds n p i).1 (chunkBounds n p i).2 n hc h
      by_cases h2 : allDec b (chunkBounds n p i).1 (chunkBounds n p i).2
      · have h2' := this.1 h2
        simp only [h1, h2, h2', if_true, if_false, ih (i + 1)]
      · have h2' : ¬ allDec b' (chunkBounds n p i).1 (chunkBounds n p i).2 := fun H => h2 (this.2 H)
        simp only [h1, h2, h2', if_true, if_false]

theorem fromDec_congr (b b' : Nat → Nat) (n p : Nat) (h : ∀ k, k < n → b k = b' k) : fromDec b n p = fromDec b' n p := by
  unfold fromDec
  by_cases hp : n ≤ p
  · simp [hp]
  · have hp' : p ≤ n := by omega
    have hf := firstBad_congr b b' n p hp' h 5 0
    simp only [hp, if_false, hf]
    have hd : decSum b p (n - p) = decSum b' p (n - p) :=
      decSum_congr b b' p (n - p) (fun k h1 h2 => h k (by omega))
    rw [hd]

theorem lexGt_congr (x x' y : Nat → Nat) (n : Nat) (h : ∀ k, k < n → x k = x' k) : lexGt x y n ↔ lexGt x' y n := by
  unfold lexGt
  constructor
  · rintro ⟨k, hk, h3, h4⟩
    exact ⟨k, hk, fun j hj => (h j (by omega)).symm.trans (h3 j hj), (h k hk) ▸ h4⟩
  · rintro ⟨k, hk, h3, h4⟩
    exact ⟨k, hk, fun j hj => (h j (by omega)).trans (h3 j hj), (h k hk).symm ▸ h4⟩

theorem decParse_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) : decParse b n = decParse b' n := by
  unfold decParse
  rw [startPos_congr b b' n h]
  by_cases h1 : n - startPos b' n < 78
  · simp only [h1, if_true, fromDec_congr b b' n _ h]
  · by_cases h2 : n - startPos b' n = 78
    · simp only [h1, h2, if_false, if_true]
      have hs : startPos b' n + 78 = n := by omega
      have hl : lexGt (fun k => b (startPos b' n + k)) maxDigit 78 ↔ lexGt (fun k => b' (startPos b' n + k)) maxDigit 78 :=
        lexGt_congr _ _ _ 78 (fun k hk => h _ (by omega))
      by_cases h3 : lexGt (fun k => b (startPos b' n + k)) maxDigit 78
      · simp [h3, hl.1 h3]
      · have h3' : ¬ lexGt (fun k => b' (startPos b' n + k)) maxDigit 78 := fun H => h3 (hl.2 H)
        simp [h3, h3', fromDec_congr b b' n _ h]
    · simp [h1, h2]

end Fv256.I
