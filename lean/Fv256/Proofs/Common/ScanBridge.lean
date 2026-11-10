import Fv256.Spec.Scan
import Fv256.Proofs.Common.SfdBridge

/-!
# Bridge: the readable `Spec.scanText` agrees with the implementation-shaped `Fv256.ScanSpec.sciParse`
(bytes as a function `Nat → Nat` plus a length, `Res` triples).

Main result `sciParse_eq`: `sciParse b n = toRes (scanText ((List.range n).map b))`.
-/

namespace Fv256.ScanBridge

open Fv256.I Fv256.Spec Fv256.SfdBridge Fv256.ScanSpec

theorem take_bl (b : Nat → Nat) (n i : Nat) (h : i ≤ n) : (bl b n).take i = bl b i := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2; simp

theorem drop_bl (b : Nat → Nat) (n i : Nat) : (bl b n).drop i = bl (fun j => b (i + j)) (n - i) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2; simp

theorem fi_range (q : Nat → Bool) : ∀ n, (List.range n).findIdx? q = (List.range n).find? q := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.findIdx?_append, List.find?_append, ih]
    by_cases h : q n
    · simp [h]
    · simp [h]

theorem bl_single (f : Nat → Nat) (m : Nat) : bl f m = [48] ↔ m = 1 ∧ f 0 = 48 := by
  match m with
  | 0 => simp [bl]
  | 1 => simp [bl, List.range_succ]
  | k + 2 =>
    have := congrArg List.length (show bl f (k + 2) = bl f (k + 2) from rfl)
    constructor
    · intro h; have := congrArg List.length h; simp [bl] at this
    · intro h; omega

/-- the index of the first `'e'` found by the readable `findIdx?` is the one `idxE` of the function view finds -/
theorem findIdx_bl (b : Nat → Nat) (n : Nat) : (bl b n).findIdx? (· == 101) = idxE b n := by
  unfold bl idxE
  rw [List.findIdx?_map, fi_range]; rfl

open Classical in
theorem sciParse_eq (b n) : sciParse b n = toRes (scanText (bl b n)) := by
  unfold sciParse scanText
  by_cases hn : n = 0
  · subst hn; simp [bl, toRes]
  · have hne : bl b n ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    simp only [hn, hne, ite_false]
    rw [← findIdx_bl]
    cases hi : (bl b n).findIdx? (· == 101) with
    | none => simp only [hi]; exact decParse_eq b n
    | some i =>
      simp only [hi]
      have hlt : i < n := by
        have := List.findIdx?_eq_some_iff_getElem.1 hi
        obtain ⟨h1, _⟩ := this; simpa using h1
      rw [take_bl b n i (by omega), decParse_eq b i]
      rcases hs : setFromDecimal (bl b i) with v | ⟨⟩ | ⟨⟩ | ⟨a, c⟩
      · simp only [toRes, Res.ok]
        rw [drop_bl]
        have hd := decParse_eq (fun j => b (i + 1 + j)) (n - (i + 1))
        by_cases hc : n - (i + 1) = 1 ∧ b (i + 1) = 48
        · have : bl (fun j => b (i + 1 + j)) (n - (i + 1)) = [48] := (bl_single _ _).2 ⟨hc.1, by simpa using hc.2⟩
          rw [this]
          simp [hc]
        · have : ¬ bl (fun j => b (i + 1 + j)) (n - (i + 1)) = [48] := fun h => hc (by have := (bl_single _ _).1 h; exact ⟨this.1, by simpa using this.2⟩)
          simp only [this, ite_false, hc]
          rw [hd]
          rcases hr : setFromDecimal (bl (fun j => b (i + 1 + j)) (n - (i + 1))) with e | ⟨⟩ | ⟨⟩ | ⟨a, c⟩
          · by_cases hco : 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e <;> simp [toRes, Res.ok, Res.range, hco]
          · simp [toRes]
          · simp [toRes]
          · simp [toRes, Res.syntax]
      · simp [toRes]
      · simp [toRes]
      · simp [toRes]


/-- The four-way result disjunction of the implementation-shaped statement is the readable `match` on `Spec.scan` of the text. -/
theorem sci_match_iff (s : List Nat) (P1 : Nat → Prop) (P2 P3 : Prop) (P4 : Nat → Nat → Prop) :
    ((∃ v, toRes (scanText s) = Res.ok v ∧ P1 v) ∨ (toRes (scanText s) = Res.eof ∧ P2) ∨ (toRes (scanText s) = Res.range ∧ P3) ∨
      (∃ lo len, toRes (scanText s) = Res.syntax lo len ∧ P4 lo len)) ↔
    (match Fv256.Spec.scan (.text s) with
     | .ok v => P1 v | .eof => P2 | .range => P3 | .badSyntax a b => P4 a b | .unsupported => False) := by
  unfold Fv256.Spec.scan
  rcases h : scanText s with v | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [h, toRes, Res.ok, Res.eof, Res.range, Res.syntax, ScanResult.ok, ScanResult.eof, ScanResult.range, ScanResult.badSyntax, ScanSource.text] <;>
    exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, h⟩ => h, fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

end Fv256.ScanBridge
