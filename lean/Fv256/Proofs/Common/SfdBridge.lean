import Fv256.Spec.SetFromDecimal
import Fv256.Spec.I
import Fv256.Spec.HexLemmas

/-!
# Bridge: the readable `Spec.setFromDecimal` (strings as byte lists) agrees with the implementation-shaped `Fv256.I.decParse`
(bytes as a function `Nat → Nat` plus a length, 19-byte chunk walk).

Main result `decParse_eq`: `decParse b n = toRes (Spec.setFromDecimal ((List.range n).map b))`.
Everything here is pure `Nat`/`List` reasoning.
-/

namespace Fv256.SfdBridge

open Fv256.I Fv256.Spec

/-- the byte list `b 0, ..., b (n-1)` -/
abbrev bl (b : Nat → Nat) (n : Nat) : List Nat := (List.range n).map b

theorem bl_length (b n) : (bl b n).length = n := by simp [bl]

theorem bl_getElem (b n k) (h : k < (bl b n).length) : (bl b n)[k] = b k := by simp [bl]

/-- the call's string `(p, n)` read as a byte list is the byte list of the function `bytesAt m p` -/
theorem bl_bytesAt (m : Janus.Arm64.Memory) (p n : Nat) :
    bl (Fv256.C.bytesAt m p) n = Janus.Spec.strBytes m p n := by
  unfold Janus.Spec.strBytes bl Fv256.C.bytesAt; simp [Janus.Arm64.Memory.readLE]

/-- the readable result type mapped to the implementation-shaped `Res` triple -/
def toRes : DecResult → Res
  | .ok v => Res.ok v
  | .eof => Res.eof
  | .range => Res.range
  | .badSyntax lo len => Res.syntax lo len

theorem toRes_eq_ok (r : DecResult) (v : Nat) : toRes r = Res.ok v ↔ r = .ok v := by
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, b⟩ <;> simp [toRes, DecResult.ok, DecResult.eof, DecResult.range, DecResult.badSyntax, Res.ok, Res.eof, Res.range, Res.syntax]

theorem toRes_eq_eof (r : DecResult) : toRes r = Res.eof ↔ r = .eof := by
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, b⟩ <;> simp [toRes, DecResult.ok, DecResult.eof, DecResult.range, DecResult.badSyntax, Res.ok, Res.eof, Res.range, Res.syntax]

theorem toRes_eq_range (r : DecResult) : toRes r = Res.range ↔ r = .range := by
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, b⟩ <;> simp [toRes, DecResult.ok, DecResult.eof, DecResult.range, DecResult.badSyntax, Res.ok, Res.eof, Res.range, Res.syntax]

theorem toRes_eq_syntax (r : DecResult) (lo len : Nat) : toRes r = Res.syntax lo len ↔ r = .badSyntax lo len := by
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, b⟩ <;> simp [toRes, DecResult.ok, DecResult.eof, DecResult.range, DecResult.badSyntax, Res.ok, Res.eof, Res.range, Res.syntax]

/-! ### leading `+` and zeros -/

theorem dropPlus_ne (c : Nat) (t : List Nat) (h : c ≠ 43) : dropPlus (c :: t) = c :: t := by
  unfold dropPlus; split
  · simp_all
  · rfl

theorem drop_plus (b n) : dropPlus (bl b n) = (bl b n).drop (plusEnd b n) := by
  cases n with
  | zero => simp [bl, dropPlus, plusEnd]
  | succ m =>
    have h0 : bl b (m + 1) = b 0 :: (bl b (m + 1)).drop 1 := by
      simp [bl, List.range_succ_eq_map, List.map_cons, List.map_map, List.drop_succ_cons]
    by_cases h : b 0 = 43
    · rw [h0]; simp [plusEnd, h, dropPlus]
    · have : plusEnd b (m + 1) = 0 := by simp [plusEnd, h]
      rw [this]
      rw [h0]
      simp only [List.drop_zero]
      exact dropPlus_ne _ _ h

theorem zerosFrom_lt (b n) : ∀ f a k, k < zerosFrom b n f a → a + k < n ∧ b (a + k) = 48 := by
  intro f
  induction f with
  | zero => intro a k h; simp [zerosFrom] at h
  | succ f ih =>
    intro a k h
    unfold zerosFrom at h
    split at h
    · rename_i hc
      cases k with
      | zero => simpa using hc
      | succ k =>
        have := ih (a + 1) k (by omega)
        refine ⟨by omega, ?_⟩
        have e : a + (k + 1) = a + 1 + k := by omega
        rw [e]; exact this.2
    · simp at h

theorem zerosFrom_le (b n f a) : zerosFrom b n f a ≤ n - a := by
  by_cases h : zerosFrom b n f a ≤ n - a
  · exact h
  · have := zerosFrom_lt b n f a (n - a) (by omega)
    omega

theorem dropWhile_zeros (b n) :
    ∀ f a, n - a ≤ f → ((bl b n).drop a).dropWhile (· == 48) = (bl b n).drop (a + zerosFrom b n f a) := by
  intro f
  induction f with
  | zero =>
    intro a h
    have : n ≤ a := by omega
    simp [zerosFrom, bl]
    rw [List.drop_eq_nil_of_le (by simpa using this)]; simp
  | succ f ih =>
    intro a h
    by_cases hc : a < n ∧ b a = 48
    · have hz : zerosFrom b n (f + 1) a = zerosFrom b n f (a + 1) + 1 := by
        simp [zerosFrom, hc]
      have hd : (bl b n).drop a = b a :: (bl b n).drop (a + 1) := by
        have : a < (bl b n).length := by simpa [bl_length] using hc.1
        rw [List.drop_eq_getElem_cons this, bl_getElem]
      rw [hd, List.dropWhile_cons, hz]
      simp [hc.2]
      rw [ih (a + 1) (by omega)]
      congr 1; omega
    · have hz : zerosFrom b n (f + 1) a = 0 := by simp [zerosFrom, hc]
      rw [hz]
      by_cases han : a < n
      · have hd : (bl b n).drop a = b a :: (bl b n).drop (a + 1) := by
          have : a < (bl b n).length := by simpa [bl_length] using han
          rw [List.drop_eq_getElem_cons this, bl_getElem]
        rw [hd, List.dropWhile_cons]
        have : ¬ b a = 48 := fun h => hc ⟨han, h⟩
        simp [this]
        exact hd.symm
      · have : (bl b n).drop a = [] := List.drop_eq_nil_of_le (by simp; omega)
        rw [this]; simp; omega

theorem startPos_le (b n) : startPos b n ≤ n := by
  unfold startPos
  have h1 := zerosFrom_le b n (n - plusEnd b n) (plusEnd b n)
  have h2 : plusEnd b n ≤ n := by unfold plusEnd; split <;> omega
  split <;> omega

theorem body_eq (b n) : body (bl b n) = (bl b n).drop (startPos b n) := by
  unfold body dropZeros
  rw [drop_plus]
  have hd := dropWhile_zeros b n (n - plusEnd b n) (plusEnd b n) (Nat.le_refl _)
  rw [hd]
  have h1 := zerosFrom_le b n (n - plusEnd b n) (plusEnd b n)
  have h2 : plusEnd b n ≤ n := by unfold plusEnd; split <;> omega
  by_cases hc : plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n) = n ∧ plusEnd b n < n
  · have hs : startPos b n = n - 1 := by unfold startPos; simp [hc]
    have hnil : (bl b n).drop (plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n)) = [] :=
      List.drop_eq_nil_of_le (by simp; omega)
    have hne : (bl b n).drop (plusEnd b n) ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    rw [hs]
    have hl := zerosFrom_lt b n (n - plusEnd b n) (plusEnd b n) (n - 1 - plusEnd b n) (by omega)
    have hlast : (bl b n).drop (n - 1) = [48] := by
      have hlt : n - 1 < (bl b n).length := by simp; omega
      rw [List.drop_eq_getElem_cons hlt, bl_getElem]
      have e : plusEnd b n + (n - 1 - plusEnd b n) = n - 1 := by omega
      rw [e] at hl
      rw [hl.2]
      have : (bl b n).drop (n - 1 + 1) = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [this]
    rw [hlast]
    rw [hnil]
    cases h : (bl b n).drop (plusEnd b n) with
    | nil => exact absurd h hne
    | cons x t => simp
  · have hs : startPos b n = plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n) := by
      unfold startPos; simp [hc]
    rw [hs]
    cases hD : (bl b n).drop (plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n)) with
    | cons x t => simp
    | nil =>
      cases hE : (bl b n).drop (plusEnd b n) with
      | nil => simp
      | cons y u =>
        exfalso
        have h3 : plusEnd b n < n := by
          have := congrArg List.length hE; simp at this; omega
        have h4 := congrArg List.length hD
        simp at h4
        exact hc ⟨by omega, h3⟩


/-! ### digits, chunks, value -/

theorem isDigit_iff (c : Nat) : isDigit c = true ↔ isDec c := by
  simp [isDigit, isDec]

theorem all_isDigit_iff (b n lo hi) (hhi : hi ≤ n) :
    (((bl b n).drop lo).take (hi - lo)).all isDigit = true ↔ allDec b lo hi := by
  rw [List.all_eq_true]
  constructor
  · intro h k hk1 hk2
    have hmem : b k ∈ ((bl b n).drop lo).take (hi - lo) := by
      rw [List.mem_iff_getElem]
      refine ⟨k - lo, ?_, ?_⟩
      · simp; omega
      · simp only [List.getElem_take, List.getElem_drop, bl_getElem]
        have : lo + (k - lo) = k := by omega
        simp [this]
    exact (isDigit_iff _).1 (h _ hmem)
  · intro h c hc
    rw [List.mem_iff_getElem] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    simp only [List.getElem_take, List.getElem_drop, bl_getElem]
    simp at hi
    exact (isDigit_iff _).2 (h _ (by omega) (by omega))

open Classical in
/-- the chunk test of `firstBadChunk` at round `i` equals the one of `firstBad` -/
noncomputable def chunkG (b : Nat → Nat) (n p : Nat) (i : Nat) : Option (Nat × Nat) :=
  if n - p ≤ 19 * i then none
  else if allDec b (chunkBounds n p i).1 (chunkBounds n p i).2 then none
  else some ((chunkBounds n p i).1, (chunkBounds n p i).2 - (chunkBounds n p i).1)

open Classical in
theorem firstBad_eq (b n p) : ∀ f i, firstBad b n p f i = (List.range f).findSome? (fun j => chunkG b n p (i + j)) := by
  intro f
  induction f with
  | zero => intro i; simp [firstBad]
  | succ f ih =>
    intro i
    rw [List.range_succ_eq_map, List.findSome?_cons]
    unfold firstBad
    by_cases h1 : n - p ≤ 19 * i
    · simp only [h1, ite_true]
      have : chunkG b n p (i + 0) = none := by simp [chunkG, h1]
      rw [this]
      simp only [List.findSome?_map]
      symm
      rw [List.findSome?_eq_none_iff]
      intro j _
      have : n - p ≤ 19 * (i + (j + 1)) := by omega
      simp only [Function.comp, chunkG, this, ite_true]
    · simp only [h1, ite_false]
      by_cases h2 : allDec b (chunkBounds n p i).1 (chunkBounds n p i).2
      · simp only [h2, ite_true]
        have : chunkG b n p (i + 0) = none := by simp [chunkG, h1, h2]
        rw [this, ih (i + 1)]
        simp only [List.findSome?_map]
        congr 1; funext j; congr 1; omega
      · simp only [h2, ite_false]
        have : chunkG b n p (i + 0) = some ((chunkBounds n p i).1, (chunkBounds n p i).2 - (chunkBounds n p i).1) := by
          simp [chunkG, h1, h2]
        rw [this]

theorem firstBadChunk_eq (b n p) :
    firstBadChunk (bl b n) p = firstBad b n p 5 0 := by
  rw [firstBad_eq]
  unfold firstBadChunk
  congr 1; funext j
  simp only [chunkG, chunkBounds, bl_length, Nat.zero_add]
  by_cases h1 : n - p ≤ 19 * j
  · simp [h1]
  · simp only [h1, ite_false]
    have hhi : n - 19 * j ≤ n := Nat.sub_le _ _
    have hall := all_isDigit_iff b n (if p + 19 ≤ n - 19 * j then n - 19 * j - 19 else p) (n - 19 * j) hhi
    by_cases h2 : allDec b (if p + 19 ≤ n - 19 * j then n - 19 * j - 19 else p) (n - 19 * j)
    · simp [h2, hall.2 h2]
    · have : ¬ ((((bl b n).drop (if p + 19 ≤ n - 19 * j then n - 19 * j - 19 else p)).take
          (n - 19 * j - (if p + 19 ≤ n - 19 * j then n - 19 * j - 19 else p))).all isDigit = true) :=
        fun h => h2 (hall.1 h)
      simp [h2, this]

theorem digitsValue_take (b n a) : ∀ m, a + m ≤ n → digitsValue (((bl b n).drop a).take m) = decSum b a m := by
  intro m
  induction m with
  | zero => intro _; simp [digitsValue, decSum]
  | succ m ih =>
    intro h
    have hlt : a + m < (bl b n).length := by rw [bl_length]; omega
    have : ((bl b n).drop a).take (m + 1) = ((bl b n).drop a).take m ++ [b (a + m)] := by
      rw [List.take_add_one]
      have : ((bl b n).drop a)[m]? = some (b (a + m)) := by
        rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega), bl_getElem]
      rw [this]; rfl
    rw [this]
    unfold digitsValue at ih ⊢
    rw [List.foldl_append, ih (by omega)]
    simp [decSum]

/-! ### the 78-digit bound -/

theorem maxDigits_length : maxDigits.length = 78 := by decide

set_option maxRecDepth 100000 in
theorem maxDigits_get : ∀ k : Fin 78, maxDigits[k.val]?.getD 0 = maxDigit k.val := by decide

theorem lt_iff_exists : ∀ (u w : List Nat) (h : u.length = w.length),
    (u < w ↔ ∃ k, ∃ hk : k < u.length, (∀ j (hj : j < k), u[j]'(by omega) = w[j]'(by omega)) ∧ u[k] < w[k]'(by omega)) := by
  intro u
  induction u with
  | nil => intro w h; cases w with
    | nil => simp
    | cons y w => simp at h
  | cons x u ih =>
    intro w h
    cases w with
    | nil => simp at h
    | cons y w =>
      simp at h
      rw [List.cons_lt_cons_iff, ih w h]
      constructor
      · rintro (h1 | ⟨h1, k, hk, h2, h3⟩)
        · exact ⟨0, by simp, by simp, by simpa using h1⟩
        · refine ⟨k + 1, by simp; omega, ?_, by simpa using h3⟩
          intro j hj
          cases j with
          | zero => simpa using h1
          | succ j => simpa using h2 j (by omega)
      · rintro ⟨k, hk, h2, h3⟩
        cases k with
        | zero => left; simpa using h3
        | succ k =>
          right
          have e : x = y := by simpa using h2 0 (by omega)
          refine ⟨e, k, by simp at hk; omega, ?_, by simpa using h3⟩
          intro j hj
          simpa using h2 (j + 1) (by omega)

theorem maxDigits_getElem (j : Nat) (hj : j < maxDigits.length) : maxDigits[j] = maxDigit j := by
  have h78 : j < 78 := by simpa [maxDigits_length] using hj
  have := maxDigits_get ⟨j, h78⟩
  simpa [List.getElem?_eq_getElem hj] using this

theorem maxDigits_lt_iff (b n sp) (hlen : n - sp = 78) :
    maxDigits < (bl b n).drop sp ↔ lexGt (fun k => b (sp + k)) maxDigit 78 := by
  have hd : ∀ j (hj : j < ((bl b n).drop sp).length), ((bl b n).drop sp)[j] = b (sp + j) := by
    intro j hj; simp
  rw [lt_iff_exists _ _ (by simp [maxDigits_length]; omega)]
  unfold lexGt
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    have hk78 : k < 78 := by simpa [maxDigits_length] using hk
    refine ⟨k, hk78, ?_, ?_⟩
    · intro j hj
      have := h1 j hj
      rw [maxDigits_getElem, hd] at this
      exact this.symm
    · rw [maxDigits_getElem, hd] at h2; exact h2
  · rintro ⟨k, hk, h1, h2⟩
    refine ⟨k, by simp [maxDigits_length]; omega, ?_, ?_⟩
    · intro j hj
      rw [maxDigits_getElem, hd]; exact (h1 j hj).symm
    · rw [maxDigits_getElem, hd]; exact h2


theorem body_length (b n) : (body (bl b n)).length = n - startPos b n := by
  rw [body_eq]; simp

open Classical in
theorem parseBody_eq (b n) : toRes (parseBody (bl b n)) = fromDec b n (startPos b n) := by
  have hsp := startPos_le b n
  unfold parseBody
  have hp : (bl b n).length - (body (bl b n)).length = startPos b n := by
    rw [body_length, bl_length]; omega
  simp only [hp]
  unfold fromDec
  by_cases hn : n ≤ startPos b n
  · have : body (bl b n) = [] := by
      rw [body_eq]; exact List.drop_eq_nil_of_le (by simp; omega)
    simp [this, hn, toRes]
  · have : body (bl b n) ≠ [] := by
      intro h; have := congrArg List.length h; rw [body_length] at this; simp at this; omega
    simp only [this, hn, ite_false]
    rw [firstBadChunk_eq b n _]
    cases hf : firstBad b n (startPos b n) 5 0 with
    | none =>
      simp only [toRes]
      have := digitsValue_take b n (startPos b n) (n - startPos b n) (by omega)
      rw [List.take_of_length_le (by simp)] at this
      rw [body_eq, this]
    | some q => simp [toRes]

open Classical in
theorem decParse_eq (b n) : decParse b n = toRes (setFromDecimal (bl b n)) := by
  have hsp := startPos_le b n
  unfold decParse setFromDecimal
  rw [body_length]
  by_cases h1 : n - startPos b n < 78
  · simp only [h1, ite_true]; exact (parseBody_eq b n).symm
  · by_cases h2 : n - startPos b n = 78
    · simp only [h2, ite_true, ite_false]
      have hl := maxDigits_lt_iff b n (startPos b n) h2
      rw [body_eq]
      by_cases h3 : lexGt (fun k => b (startPos b n + k)) maxDigit 78
      · simp [h3, hl.2 h3, toRes]
      · have : ¬ maxDigits < (bl b n).drop (startPos b n) := fun h => h3 (hl.1 h)
        simp only [h3, this, ite_false]
        have h78 : ¬ (78 : Nat) < 78 := by omega
        simp only [h78, ite_false]
        exact (parseBody_eq b n).symm
    · have : ¬ n - startPos b n = 78 := h2
      simp [h1, h2, toRes]

end Fv256.SfdBridge
