import Janus
import Fv256.Spec.Amd64.CallSites.Live

/-! Call-site helpers for the `∀ L b` Live contracts (U-WITNESS-CALLSITE), amd64: `L := []` makes `LiveSep` trivial on one side. -/

open Janus Janus.Amd64 Janus.Contracts

namespace Fv256.CallSites

scoped instance (s : State) (stack nargs : Nat) : Decidable (CallOK64 s stack nargs) := by unfold CallOK64; infer_instance
scoped instance (m : Memory) (t : Nat) : Decidable (TypeOK m t) := by unfold TypeOK; infer_instance
scoped instance (s : State) (adj : Nat) : Decidable (GuardOK64 s adj) := by unfold GuardOK64; infer_instance

scoped instance outsideDec (a n : Nat) : ∀ L : List (Nat × Nat), Decidable (Outside a n L)
  | [] => isTrue trivial
  | (lo, hi) :: rs =>
    haveI := outsideDec a n rs
    inferInstanceAs (Decidable ((a + n ≤ lo ∨ hi ≤ a) ∧ Outside a n rs))

scoped instance (s : State) (adj : Nat) : Decidable (Janus.Amd64.GoABI.StackGuardOK s adj) :=
  decidable_of_iff ((s.regs Janus.Amd64.GoABI.regG).toNat + Janus.Amd64.GoABI.stackguard0Offset + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible ((s.regs Janus.Amd64.GoABI.regG).toNat + Janus.Amd64.GoABI.stackguard0Offset) 8 false = true ∧
      Janus.Amd64.GoABI.stackguard0 s + adj < (s.regs Janus.Amd64.GoABI.regSP).toNat)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.noWrap, h.readable, h.below⟩⟩
scoped instance (s : State) (d nargs : Nat) : Decidable (MemAmd64.CallOK s d nargs) := by unfold MemAmd64.CallOK; infer_instance
scoped instance (s : State) (d nargs : Nat) : Decidable (MemAmd64.EqPre d nargs s) := by unfold MemAmd64.EqPre; infer_instance
scoped instance (s : State) (d nargs a n : Nat) : Decidable (MemAmd64.Input s d nargs a n) := by unfold MemAmd64.Input; infer_instance
scoped instance (m : Memory) : Decidable (IfaceModel.Desc m) := by unfold IfaceModel.Desc; infer_instance
scoped instance (m : Memory) (p n : Nat) : Decidable (Cmpstring.StrOK m p n) := by unfold Cmpstring.StrOK; infer_instance

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

/-! ### Single-conjunct wrappers of the contracts' preconditions (the auditor matches the whole `pre s_c` against ONE conjunct; reducible for its first `isDefEq`). -/

theorem strsIn_of {m : Memory} {buf : Nat} {xs : List (Nat × Nat)} (h : ∀ x ∈ xs, StrIn m x.1 x.2) (hb : buf = 0) :
    StrsIn m buf xs := fun x hx => ⟨h x hx, fun hh => absurd hb hh⟩

end Fv256.CallSites
