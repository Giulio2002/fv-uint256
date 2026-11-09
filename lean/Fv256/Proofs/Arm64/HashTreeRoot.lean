import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).HashTreeRoot() ([32]byte, error)` (arm64)

**Guarantee.** For every receiver `z` (`X0`) with 32 readable bytes, a Go call whose stack window `[SP-88, SP+40)` is writable and
aligned (`StackOK s 88 40`) and does not overlap `z`, and the Go frame-pointer convention: the call returns, obeys the ABI, the 32 result
bytes at `SP+8` (the caller's frame) read as the little-endian number equal to the number at `z` (the SSZ encoding of a `uint256`), the
returned `error` is `nil` (`X0 = X1 = 0`), and no byte changes outside the result and the frame.

**Non-vacuity.** `Witness.nonvacuous` / `Witness.returns`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.HashTreeRoot

theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => Ptr32 s.mem z false ∧ StackOK s 88 40 ∧ Disjoint z.toNat 32 (s.sp.toNat - 88) 128 ∧ s.regs 29 = s.sp - 8#64)
      (fun s s' => s'.mem.readLE (s.sp.toNat + 8) 32 = val256 s.mem z.toNat ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
        Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 88) 88) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hal, hb, ha, hw⟩, hdis, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run
  refine ⟨?_, ?_⟩
  · simp only [val256, Util.readLE_32]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Util.readLE8_mod, Nat.reducePow]
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 28 then BitVec.ofNat 64 wg else if i = 29 then BitVec.ofNat 64 wsp - 8#64
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem hpre : Ptr32 s0.mem z false ∧ StackOK s0 88 40 ∧ Disjoint z.toNat 32 (s0.sp.toNat - 88) 128 ∧
    s0.regs 29 = s0.sp - 8#64 :=
  ⟨⟨by decide, by decide⟩, by unfold StackOK; decide, by unfold Disjoint; decide, rfl⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧
    (Ptr32 s.mem z false ∧ StackOK s 88 40 ∧ Disjoint z.toNat 32 (s.sp.toNat - 88) 128 ∧ s.regs 29 = s.sp - 8#64) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.mem.readLE (s.sp.toNat + 8) 32 = val256 s.mem z.toNat ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
        Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 88) 88 :=
  ⟨ret, s0, z, hret, setup, hpre,
    correctness z ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.mem.readLE (s0.sp.toNat + 8) 32 = val256 s0.mem z.toNat ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem (s0.sp.toNat + 8) 32 (s0.sp.toNat - 88) 88 := by
  refine (correctness z ret hret s0 setup hpre).mono ?_
  intro s' h
  exact h

end Witness

end Fv256.Arm64.HashTreeRoot
