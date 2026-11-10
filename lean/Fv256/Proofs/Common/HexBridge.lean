import Fv256.Spec.SetFromHex
import Fv256.Spec.C
import Fv256.Spec.HexLemmas

/-!
# Bridge: the readable `Spec.setFromHex` (strings as byte lists) agrees with the implementation-shaped `Fv256.C.parseHex`
(bytes as a function `Nat → Nat` plus a length, results as `Except Nat Nat` with numbered errors).

Main result `parseHex_eq`: `parseHex b n = toExcept (Spec.setFromHex ((List.range n).map b))`.
-/

namespace Fv256.HexBridge

open Fv256.C Fv256.Spec

/-- the byte list `b 0, ..., b (n-1)` -/
abbrev bl (b : Nat → Nat) (n : Nat) : List Nat := (List.range n).map b

/-- the call's string `(p, n)` read as a byte list is the byte list of the function `bytesAt m p` -/
theorem bl_bytesAt (m : Janus.Arm64.Memory) (p n : Nat) : bl (bytesAt m p) n = Janus.Spec.strBytes m p n := by
  unfold Janus.Spec.strBytes bl bytesAt; simp [Janus.Arm64.Memory.readLE]

/-- the readable result mapped to the numbered-error encoding of `parseHex` -/
def toExcept : HexResult → Except Nat Nat
  | .ok v => .ok v
  | .error e => .error e.tag

theorem toExcept_eq_ok (r : HexResult) (v : Nat) : toExcept r = .ok v ↔ r = .ok v := by
  cases r <;> simp [toExcept]

theorem toExcept_eq_error (r : HexResult) (e : Nat) : toExcept r = .error e ↔ ∃ e' : HexError, r = .error e' ∧ e'.tag = e := by
  cases r with
  | ok v => simp [toExcept]
  | error e' => simp [toExcept]

theorem hexNib_eq (c : Nat) : hexNib c = hexDigitValue c := rfl

/-- the digit bytes `b a, ..., b (a + m - 1)` -/
abbrev dl (b : Nat → Nat) (a m : Nat) : List Nat := (List.range m).map fun k => b (a + k)

theorem bl_succ2 (b m) : bl b (m + 2) = b 0 :: b 1 :: dl b 2 m := by
  simp [bl, dl, List.range_succ_eq_map, List.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]

theorem dl_length (b a m) : (dl b a m).length = m := by simp [dl]

theorem dl_head (b a m) (h : 0 < m) : (dl b a m).head? = some (b a) := by
  cases m with
  | zero => omega
  | succ m => simp [dl, List.range_succ_eq_map]

theorem dl_foldl (b a m) : (dl b a m).foldl (fun acc c => acc * 16 + (hexDigitValue c).getD 0) 0 = hexSum b a m := by
  induction m with
  | zero => simp [dl, hexSum]
  | succ m ih =>
    unfold dl at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp [hexSum, hexDigit, hexNib_eq]

theorem dl_all (b a m) : (dl b a m).all (fun c => (hexDigitValue c).isSome) = true ↔ allHex b a (a + m) := by
  rw [List.all_eq_true]
  constructor
  · intro h k hk1 hk2
    have := h (b k) (by
      rw [dl, List.mem_map]; exact ⟨k - a, by simp; omega, by congr 1; omega⟩)
    simpa [hexNib_eq] using this
  · intro h c hc
    rw [dl, List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    simp at hi
    have := h (a + i) (by omega) (by omega)
    simpa [hexNib_eq] using this

open Classical in
theorem parseHex_eq (b n) : parseHex b n = toExcept (setFromHex (bl b n)) := by
  match n with
  | 0 => simp [parseHex, setFromHex, toExcept, HexError.tag, HexError.emptyString, HexError.missingPrefix, HexError.emptyNumber, HexError.leadingZero, HexError.big256Range, HexError.badSyntax, bl]
  | 1 =>
    simp [parseHex, setFromHex, toExcept, HexError.tag, HexError.emptyString, HexError.missingPrefix, HexError.emptyNumber, HexError.leadingZero, HexError.big256Range, HexError.badSyntax, bl, List.range_succ]
  | m + 2 =>
    rw [bl_succ2]
    unfold parseHex setFromHex
    simp only [show m + 2 ≠ 0 by omega, ite_false]
    by_cases hp : (b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88))
    · have hp' : (m + 2 < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := Or.inr hp
      simp [hp, toExcept, HexError.tag, HexError.emptyString, HexError.missingPrefix, HexError.emptyNumber, HexError.leadingZero, HexError.big256Range, HexError.badSyntax]
    · have hp' : ¬ (m + 2 < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by
        intro h; rcases h with h | h; omega; exact hp h
      simp only [hp, ite_false]
      by_cases h0 : m = 0
      · subst h0; simp [toExcept, HexError.tag, HexError.emptyString, HexError.missingPrefix, HexError.emptyNumber, HexError.leadingZero, HexError.big256Range, HexError.badSyntax]
      · have hd : dl b 2 m ≠ [] := by
          intro h; have := congrArg List.length h; simp at this; omega
        have hne : ¬ (m + 2 = 2) := by omega
        simp only [hne, ite_false, hd]
        have hlen := dl_length b 2 m
        have hm2 : ¬ (m + 2 < 2) := by omega
        simp only [hlen]
        by_cases h3 : (1 < m ∧ (dl b 2 m).head? = some 48)
        · have : 3 < m + 2 ∧ b 2 = 48 := by
            rw [dl_head b 2 m (by omega)] at h3
            refine ⟨by omega, ?_⟩
            have := h3.2; simpa using this
          simp [h3, this, hm2, toExcept, HexError.tag, HexError.emptyString, HexError.missingPrefix, HexError.emptyNumber, HexError.leadingZero, HexError.big256Range, HexError.badSyntax]
        · have : ¬ (3 < m + 2 ∧ b 2 = 48) := by
            intro h; apply h3
            refine ⟨by omega, ?_⟩
            rw [dl_head b 2 m (by omega)]; simp [h.2]
          simp only [h3, this, ite_false]
          by_cases h4 : 64 < m
          · have : 66 < m + 2 := by omega
            simp [h4, this, hm2, toExcept, HexError.tag, HexError.emptyString, HexError.missingPrefix, HexError.emptyNumber, HexError.leadingZero, HexError.big256Range, HexError.badSyntax]
          · have : ¬ 66 < m + 2 := by omega
            simp only [h4, this, ite_false]
            have hall := dl_all b 2 m
            by_cases h5 : allHex b 2 (m + 2)
            · have h6 : (dl b 2 m).all (fun c => (hexDigitValue c).isSome) = true := by
                rw [hall]; simpa [Nat.add_comm] using h5
              simp only [h6, ite_true]
              simp only [show ((2 : Nat) + m) = m + 2 by omega] at hall
              simp [h5, hm2, dl_foldl, toExcept]
            · have h6 : ¬ (dl b 2 m).all (fun c => (hexDigitValue c).isSome) = true := by
                intro h; apply h5; have := hall.1 h; simpa [Nat.add_comm] using this
              simp [h5, h6, hm2, toExcept, HexError.tag, HexError.emptyString, HexError.missingPrefix, HexError.emptyNumber, HexError.leadingZero, HexError.big256Range, HexError.badSyntax]

end Fv256.HexBridge
