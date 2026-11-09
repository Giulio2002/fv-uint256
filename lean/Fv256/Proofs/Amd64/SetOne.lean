import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).SetOne() *Int` (amd64): `z = Fv256.Spec.one`

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) and every Go call state such that the return-address slot
is writable, the 32 bytes at `z` are writable, those at `x` readable (below `2^48`), `z` does not overlap the return-address
slot, and `z`, `x` are equal or disjoint, the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number
at `z` afterwards is `Fv256.Spec.one` of the number at `x` before the call, and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous` (in `Fv256/Amd64/SetOne.lean`): a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding `1`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetOne

theorem correctness_proof (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧
        Disjoint z 32 (s.regs regSP) 8)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.one ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, hds⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Disjoint] at *
  all_goals first | (exfalso; omega) | (janus64_run [Util.readLE_32]; all_goals (refine ⟨?_, ?_⟩; (· simp [Spec.one]); (· simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self])))

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Disjoint z 32 (s0.regs regSP) 8 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Disjoint z 32 (s.regs regSP) 8) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.one ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, hret, setup, hpre,
    correctness_proof z ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 1 := by
  refine (correctness_proof z ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  try simp only [valueAt]
  try decide

end Wit

end Fv256.Amd64.SetOne

