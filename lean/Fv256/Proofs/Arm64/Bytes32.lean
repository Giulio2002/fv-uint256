import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).Bytes32() [32]byte` (arm64)

**Guarantee.** For every receiver `z` (`X0`) and every Go call such that the 32 bytes at `z` are readable (below `2^48`), the stack
window `[SP-56, SP+40)` (the 48-byte frame, a local copy of the array, and the 32 result bytes the callee returns in the caller's
frame at `SP+8`) is writable and aligned (`StackOK s 56 40`), that window does not overlap `z`, and the frame pointer is the
caller's (`X29 = SP - 8`, the Go arm64 convention): the call returns (no fault, no panic), obeys the ABI, the 32 result bytes at
`SP+8` read as the big-endian number (`Fv256.Spec.fromBE`) equal to the number at `z` (read before the call), and no byte changes
outside the result bytes and the frame (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Bytes32

theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => Ptr32 s.mem z false ∧ StackOK s 56 40 ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 96 ∧ s.regs 29 = s.sp - 8#64)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (s.sp.toNat + 8 + i) 1) 32 = val256 s.mem z.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 56) 56) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hal, hb, ha, hw⟩, hdis, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run
  refine ⟨?_, ?_⟩
  · rw [Util.be32_rev]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    rw [Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _),
      Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _),
      Util.rev8_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _)]
    omega
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

theorem hpre : Ptr32 s0.mem z false ∧ StackOK s0 56 40 ∧ Disjoint z.toNat 32 (s0.sp.toNat - 56) 96 ∧
    s0.regs 29 = s0.sp - 8#64 :=
  ⟨⟨by decide, by decide⟩, by unfold StackOK; decide, by unfold Disjoint; decide, rfl⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧
    (Ptr32 s.mem z false ∧ StackOK s 56 40 ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 96 ∧ s.regs 29 = s.sp - 8#64) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Spec.fromBE (fun i => s'.mem.readLE (s.sp.toNat + 8 + i) 1) 32 = val256 s.mem z.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 56) 56 :=
  ⟨ret, s0, z, hret, setup, hpre,
    correctness z ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Fv256.Spec.fromBE (fun i => s'.mem.readLE (s0.sp.toNat + 8 + i) 1) 32 = val256 s0.mem z.toNat ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem (s0.sp.toNat + 8) 32 (s0.sp.toNat - 56) 56 :=
  correctness z ret hret s0 setup hpre

end Witness

end Fv256.Arm64.Bytes32
