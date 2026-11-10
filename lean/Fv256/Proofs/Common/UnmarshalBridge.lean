import Fv256.Spec.UnmarshalJSON
import Fv256.Spec.HexLemmas

/-!
# Bridges for `UnmarshalText` / `UnmarshalJSON`

The readable predicates on byte lists (`hasHexPrefix`, `isQuoted`) agree with the memory-level ones used by the implementation-shaped
statements (`IsHex m p n`: `n >= 2`, byte `0` is `'0'`, byte `1` is `'x'` or `'X'`; `Quoted m p n`: `n >= 2`, first and last byte are `"`),
and cutting the quotes off the byte list is reading the string `(p + 1, n - 2)`.
-/

namespace Fv256.UnmarshalBridge

open Fv256.Spec

theorem strBytes_eq (m : Janus.Arm64.Memory) (p n : Nat) :
    Janus.Spec.strBytes m p n = (List.range n).map fun k => m.readLE (p + k) 1 := by
  unfold Janus.Spec.strBytes; simp [Janus.Arm64.Memory.readLE]

theorem hex_cons2 (a b : Nat) (t : List Nat) : hasHexPrefix (a :: b :: t) = true ↔ a = 48 ∧ (b = 120 ∨ b = 88) := by
  by_cases ha : a = 48
  · subst ha; simp [hasHexPrefix]
  · have : hasHexPrefix (a :: b :: t) = false := by
      unfold hasHexPrefix
      split
      · rename_i c t' h; simp at h; omega
      · rfl
    simp [this, ha]

theorem hasHexPrefix_iff (m : Janus.Arm64.Memory) (p n : Nat) :
    hasHexPrefix (Janus.Spec.strBytes m p n) = true ↔
      (2 ≤ n ∧ m.readLE p 1 = 48 ∧ (m.readLE (p + 1) 1 = 120 ∨ m.readLE (p + 1) 1 = 88)) := by
  rw [strBytes_eq]
  match n with
  | 0 => simp [hasHexPrefix]
  | 1 => simp [hasHexPrefix, List.range_succ]
  | k + 2 =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def]
    rw [hex_cons2]
    simp

theorem quoted_iff (m : Janus.Arm64.Memory) (p n : Nat) :
    isQuoted (Janus.Spec.strBytes m p n) = true ↔
      (2 ≤ n ∧ m.readLE p 1 = 34 ∧ m.readLE (n + p - 1) 1 = 34) := by
  rw [strBytes_eq]
  unfold isQuoted
  by_cases hn : 2 ≤ n
  · have h1 : (List.map (fun k => m.readLE (p + k) 1) (List.range n)).head? = some (m.readLE p 1) := by
      cases n with
      | zero => omega
      | succ n => simp [List.range_succ_eq_map]
    have h2 : (List.map (fun k => m.readLE (p + k) 1) (List.range n)).getLast? = some (m.readLE (n + p - 1) 1) := by
      rw [List.getLast?_eq_getElem?]
      simp only [List.length_map, List.length_range]
      rw [List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some]
      congr 2; omega
    rw [h1, h2]
    simp [hn]
  · have : ¬ 2 ≤ (List.map (fun k => m.readLE (p + k) 1) (List.range n)).length := by simpa using hn
    simp [hn]

theorem quoted_iff_arm (m : Janus.Arm64.Memory) (p n : Nat) :
    isQuoted (Janus.Spec.strBytes m p n) = true ↔
      (2 ≤ n ∧ m.readLE p 1 = 34 ∧ m.readLE (p + n - 1) 1 = 34) := by
  rw [quoted_iff, Nat.add_comm n p]

theorem inner_eq (m : Janus.Arm64.Memory) (p n : Nat) (hn : 2 ≤ n) :
    ((Janus.Spec.strBytes m p n).drop 1).dropLast = Janus.Spec.strBytes m (p + 1) (n - 2) := by
  rw [strBytes_eq, strBytes_eq]
  apply List.ext_getElem
  · simp only [List.length_dropLast, List.length_drop, List.length_map, List.length_range]; omega
  · intro i h1 h2
    simp only [List.getElem_dropLast, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [Nat.add_assoc]

end Fv256.UnmarshalBridge
