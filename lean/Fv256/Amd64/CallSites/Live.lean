import Janus

/-! Call-site helpers for the `∀ L b` Live contracts (U-WITNESS-CALLSITE), amd64: `L := []` makes `LiveSep` trivial on one side. -/

open Janus Janus.Amd64 Janus.Contracts

namespace Fv256.CallSites

theorem liveSep_nil (win : List (Nat × Nat)) : LiveSep [] win := fun r h => by simp at h

theorem liveSep_one {a e : Nat} {rt : List (Nat × Nat)} (h : Outside a (e - a) rt) : LiveSep [(a, e)] rt := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h

theorem liveSep_two {a e c f : Nat} {rt : List (Nat × Nat)} (h1 : Outside a (e - a) rt) (h2 : Outside c (f - c) rt) :
    LiveSep [(a, e), (c, f)] rt := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h2

end Fv256.CallSites
