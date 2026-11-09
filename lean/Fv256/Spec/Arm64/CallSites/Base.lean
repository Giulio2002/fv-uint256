import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.Contracts Janus.Spec

namespace Fv256.Arm64.CallSites

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
@[reducible] def MakesliceSite (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  MakeslicePre stack s ∧ Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s

open Janus.Contracts in
@[reducible] def ConvT64Site (R : Janus.Spec.Type.IfaceModel) (H : RtReady) (s : State) : Prop :=
  Iface.RTPre R 1 s ∧ Ready H R.priv [(s.regs 0).toNat] s

open Janus.Contracts in
@[reducible] def ErrorfLiveSite (R : RtInv) (addr stack : Nat) (tErr iErr tInt iWrap Fl Fm B : Nat) (L : List (Nat × Nat)) (b : Nat)
    (s : State) : Prop :=
  CallOK s stack 5 ∧ StackRoom s stack 5 ∧
    Errorf.ArgsOK (Errorf.Env.mk tErr iErr tInt iWrap) Fl Fm B s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (s.regs 3).toNat (s.regs 4).toNat ∧
    ReadsOutside (Errorf.errorfReads s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (calleeStack s stack 5) ∧
    Errorf.ReadsSafe R L (Errorf.errorfReads s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, (s.regs 3).toNat, (s.regs 4).toNat] L b
      (Errorf.errorfCost s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (s.regs 28).toNat s.mem (calleeStack s stack 5)

end Fv256.Arm64.CallSites
