import Fv256.SpecScan
import Fv256.IndexByteSpec

/-!
# `sciParse` and the result of `IndexByteString` (Extracted-free)
-/

open Fv256.I Fv256.ScanSpec Fv256.IndexByte

namespace Fv256.Amd64.ScanIdx

theorem indexOf_none (b : Nat → Nat) (n : Nat) (hn : n < 2 ^ 64 - 1) (h : indexOfNat b n 101 = 2 ^ 64 - 1) :
    idxE b n = none := by
  unfold indexOfNat at h
  unfold idxE
  cases hf : (List.range n).find? (fun i => b i == 101 % 256) with
  | none => simpa using hf
  | some i =>
    rw [hf] at h
    have hi : i ∈ List.range n := List.mem_of_find?_eq_some hf
    have := List.mem_range.1 hi
    simp only at h
    omega

theorem indexOf_some (b : Nat → Nat) (n : Nat) (hn : n < 2 ^ 64 - 1) (h : indexOfNat b n 101 ≠ 2 ^ 64 - 1) :
    ∃ i, idxE b n = some i ∧ indexOfNat b n 101 = i ∧ i < n := by
  unfold indexOfNat at h ⊢
  unfold idxE
  cases hf : (List.range n).find? (fun i => b i == 101 % 256) with
  | none => rw [hf] at h; exact absurd rfl h
  | some i =>
    have hi : i ∈ List.range n := List.mem_of_find?_eq_some hf
    refine ⟨i, ?_, ?_, List.mem_range.1 hi⟩
    · simpa using hf
    · simp

theorem sciParse_none (b : Nat → Nat) (n : Nat) (hn : n ≠ 0) (h : idxE b n = none) : sciParse b n = decParse b n := by
  simp [sciParse, hn, h]

theorem idxE_byte (b : Nat → Nat) (n i : Nat) (h : idxE b n = some i) : i < n ∧ b i = 101 := by
  unfold idxE at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  exact ⟨List.mem_range.1 hm, by simpa using hp⟩

end Fv256.Amd64.ScanIdx
