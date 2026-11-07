import Janus

/-!
# Extracted-free helpers for the arm64 call-site conjuncts (U-WITNESS-CALLSITE)
-/

open Janus Janus.Arm64 Janus.Contracts Janus.Spec

namespace Fv256.Arm64.CallSites

/-- `CallOK` componentwise decidable (all Nat/Bool facts): use `callOK_of` with `by decide` for each part. -/
theorem callOK_of {s : State} {stack nargs : Nat} (h1 : (s.regs 30).toNat % 4 = 0) (h2 : (s.regs 30).toNat < 2 ^ 48)
    (h3 : s.sp.toNat % 16 = 0) (h4 : stack ≤ s.sp.toNat) (h5 : 8 ≤ stack) (h6 : s.sp.toNat + 8 + 8 * nargs ≤ 2 ^ 48)
    (h7 : s.mem.accessible (s.sp.toNat - stack) (stack + 8 + 8 * nargs) true = true) : CallOK s stack nargs :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem typeOK_of {m : Memory} {t : Nat} (h1 : t + 16 ≤ 2 ^ 48) (h2 : m.accessible t 16 false = true) : TypeOK m t := ⟨h1, h2⟩

theorem guardOK_of {s : State} {adj : Nat} (h1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (h2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true) (h3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + adj < s.sp.toNat) :
    GuardOK s adj := ⟨h1, h2, h3⟩

theorem liveSep_nil (win : List (Nat × Nat)) : LiveSep [] win := fun r hr => absurd hr (by simp)


/-! ### Single-conjunct wrappers of the contracts' preconditions

The auditor matches the contract's whole `pre s_c` against ONE conjunct of the witness (`findConj`), after flattening the witness's
conjunctions; so a multi-part precondition is written through one of these `@[reducible]` defs (reducible: the auditor's first
`isDefEq` is at reducible transparency). Each is the contract's own `pre`, with the contract's arguments. -/

open Janus.Contracts in
@[reducible] def NewobjectSite (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  NewobjectPre stack s ∧ Ready H rt [(s.regs 0).toNat] s

open Janus.Contracts in
@[reducible] def NewobjectLiveSite (R : RtInv) (addr stack : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre stack s ∧ StackRoom s stack 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s stack 1)

open Janus.Contracts in
@[reducible] def MallocgcLiveSite (R : RtInv) (addr stack : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MallocgcPre stack s ∧ StackRoom s stack 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
      (s.regs 28).toNat s.mem (calleeStack s stack 3)

open Janus.Contracts in
@[reducible] def MemmoveLiveSite (R : RtInv) (addr d : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  Mem.EqPre d 3 s ∧
    LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s d 3) ∧
    Mem.Input s d 3 (s.regs 1).toNat (s.regs 2).toNat ∧
    LiveDest R L s d 3 (s.regs 0).toNat (s.regs 2).toNat

open Janus.Contracts in
@[reducible] def WbLiveSite (R : RtInv) (addr stack n : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s stack 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    LiveSep L [(s.sp.toNat - stack, s.sp.toNat - 8)] ∧ LiveSep [(s.sp.toNat - stack, s.sp.toNat - 8)] R.rt

open Janus.Contracts in
@[reducible] def IfaceeqSite (R : Janus.Spec.Type.IfaceModel) (s : State) : Prop :=
  Iface.RTPre R 3 s ∧ ((s.regs 0).toNat ≠ 0 →
      (s.regs 0).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 16 false = true ∧
      (s.mem.readLE ((s.regs 0).toNat + 8) 8 ≠ 0) ∧
      Iface.EqOK R s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.regs 1).toNat (s.regs 2).toNat)


open Janus.Contracts in
theorem strsIn_of {m : Memory} {buf : Nat} {xs : List (Nat × Nat)} (h : ∀ x ∈ xs, StrIn m x.1 x.2) (hb : buf = 0) :
    StrsIn m buf xs := fun x hx => ⟨h x hx, fun hh => absurd hb hh⟩

open Janus.Contracts in
@[reducible] def MakesliceSite (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  MakeslicePre stack s ∧ Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s

end Fv256.Arm64.CallSites
