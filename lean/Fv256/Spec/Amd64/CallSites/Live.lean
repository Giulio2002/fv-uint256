import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Contracts

namespace Fv256.CallSites

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

@[reducible] def MakesliceSite (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  MakeslicePre64 stack s ∧ Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s

@[reducible] def ConvT64Site (R : Janus.Spec.Type.IfaceModel) (H : RtReady) (s : State) : Prop :=
  IfaceAmd64.RTPre R 1 s ∧ Ready64 H R.priv [(s.regs 0).toNat] s

@[reducible] def ErrorfLiveSite (R : RtInv) (addr stack : Nat) (tErr iErr tInt iWrap Fl Fm B : Nat) (L : List (Nat × Nat)) (b : Nat)
    (s : State) : Prop :=
  CallOK64 s stack 5 ∧ ErrorfAmd64.RetLow s ∧ StackRoom64 s stack 5 ∧
    Errorf.ArgsOK (Errorf.Env.mk tErr iErr tInt iWrap) Fl Fm B s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat (s.regs 7).toNat (s.regs 6).toNat ∧
    ReadsOutside (Errorf.errorfReads s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (liveWin64 s stack 5) ∧
    Errorf.ReadsSafe R L (Errorf.errorfReads s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat, (s.regs 7).toNat, (s.regs 6).toNat] L b
      (Errorf.errorfCost s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (s.regs 14).toNat s.mem
      (liveWin64 s stack 5)

end Fv256.CallSites
