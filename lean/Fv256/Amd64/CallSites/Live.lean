import Janus

/-! Call-site helpers for the `∀ L b` Live contracts (U-WITNESS-CALLSITE), amd64: `L := []` makes `LiveSep` trivial on one side. -/

open Janus Janus.Amd64 Janus.Contracts

namespace Fv256.CallSites

instance (s : State) (stack nargs : Nat) : Decidable (CallOK64 s stack nargs) := by unfold CallOK64; infer_instance
instance (m : Memory) (t : Nat) : Decidable (TypeOK m t) := by unfold TypeOK; infer_instance
instance (s : State) (adj : Nat) : Decidable (GuardOK64 s adj) := by unfold GuardOK64; infer_instance

instance outsideDec (a n : Nat) : ∀ L : List (Nat × Nat), Decidable (Outside a n L)
  | [] => isTrue trivial
  | (lo, hi) :: rs =>
    haveI := outsideDec a n rs
    inferInstanceAs (Decidable ((a + n ≤ lo ∨ hi ≤ a) ∧ Outside a n rs))

instance (s : State) (adj : Nat) : Decidable (Janus.Amd64.GoABI.StackGuardOK s adj) :=
  decidable_of_iff ((s.regs Janus.Amd64.GoABI.regG).toNat + Janus.Amd64.GoABI.stackguard0Offset + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible ((s.regs Janus.Amd64.GoABI.regG).toNat + Janus.Amd64.GoABI.stackguard0Offset) 8 false = true ∧
      Janus.Amd64.GoABI.stackguard0 s + adj < (s.regs Janus.Amd64.GoABI.regSP).toNat)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.noWrap, h.readable, h.below⟩⟩
instance (s : State) (d nargs : Nat) : Decidable (MemAmd64.CallOK s d nargs) := by unfold MemAmd64.CallOK; infer_instance
instance (s : State) (d nargs : Nat) : Decidable (MemAmd64.EqPre d nargs s) := by unfold MemAmd64.EqPre; infer_instance
instance (s : State) (d nargs a n : Nat) : Decidable (MemAmd64.Input s d nargs a n) := by unfold MemAmd64.Input; infer_instance
instance (m : Memory) : Decidable (IfaceModel.Desc m) := by unfold IfaceModel.Desc; infer_instance
instance (m : Memory) (p n : Nat) : Decidable (Cmpstring.StrOK m p n) := by unfold Cmpstring.StrOK; infer_instance

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

@[reducible] def NewobjectSite (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  NewobjectPre64 stack s ∧ Ready64 H rt [(s.regs 0).toNat] s

@[reducible] def NewobjectLiveSite (R : RtInv) (addr stack : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre64 stack s ∧ StackRoom64 s stack 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound64 s) (s.regs 14).toNat s.mem (liveWin64 s stack 1)

@[reducible] def MallocgcLiveSite (R : RtInv) (addr stack : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MallocgcPre64 stack s ∧ StackRoom64 s stack 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s) (s.regs 14).toNat s.mem (liveWin64 s stack 3)

@[reducible] def MemmoveLiveSite (R : RtInv) (addr d : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MemPre64 d 3 s ∧
    LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s d 3) ∧
    MemAmd64.Input s d 3 (s.regs 3).toNat (s.regs 1).toNat ∧
    LiveDest64 R L s d 3 (s.regs 0).toNat (s.regs 1).toNat

@[reducible] def WbLiveSite (R : RtInv) (addr stack n : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK64 s stack 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    LiveSep L [((s.regs 4).toNat - stack, (s.regs 4).toNat + 8)] ∧ LiveSep [((s.regs 4).toNat - stack, (s.regs 4).toNat + 8)] R.rt

@[reducible] def IfaceeqSite (R : Janus.Spec.Type.IfaceModel) (s : State) : Prop :=
  IfaceAmd64.RTPre R 3 s ∧ ((s.regs 0).toNat ≠ 0 →
      (s.regs 0).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 16 false = true ∧
      (s.mem.readLE ((s.regs 0).toNat + 8) 8 ≠ 0) ∧
      Iface.EqOK R s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.regs 3).toNat (s.regs 1).toNat)

end Fv256.CallSites
