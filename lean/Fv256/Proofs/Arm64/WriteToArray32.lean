import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).WriteToArray32(dest *[32]byte)` (arm64)

**Guarantee.** For all pointers `z` (the receiver, `X0`) and `dest` (`X1`) such that the 32 bytes at `z` are readable, the 32
bytes at `dest` are writable (both below `2^48`) and the two ranges are disjoint, the call returns (no fault, no panic), obeys
the ABI, the 32 bytes at `dest` afterwards read as the big-endian number `Fv256.Spec.fromBE` equal to the number at `z` (read
before the call), and no byte changes outside `dest[0..32)`.
(The compiled code interleaves its loads and stores, so overlapping `z` and `dest` is outside the guarantee.)

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.WriteToArray32

theorem correctness (z dest : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, dest]
      (fun s => Ptr32 s.mem z false ∧ Ptr32 s.mem dest true ∧ Disjoint z.toNat 32 dest.toNat 32)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (dest.toNat + i) 1) 32 = val256 s.mem z.toNat ∧
        OnlyWrites s.mem s'.mem dest.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hd, hd'⟩, hdis⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run
  rw [Util.be32_rev]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  simp only [Nat.reducePow]
  rw [Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _),
    Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _),
    Util.rev8_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _)]
  omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def dest : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then dest
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dest] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z false ∧ Ptr32 s0.mem dest true ∧ Disjoint z.toNat 32 dest.toNat 32 :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z dest : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dest] s ∧
    (Ptr32 s.mem z false ∧ Ptr32 s.mem dest true ∧ Disjoint z.toNat 32 dest.toNat 32) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Spec.fromBE (fun i => s'.mem.readLE (dest.toNat + i) 1) 32 = val256 s.mem z.toNat ∧
        OnlyWrites s.mem s'.mem dest.toNat 32 :=
  ⟨ret, s0, z, dest, hret, setup, hpre,
    correctness z dest ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Fv256.Spec.fromBE (fun i => s'.mem.readLE (dest.toNat + i) 1) 32 = val256 s0.mem z.toNat ∧
      OnlyWrites s0.mem s'.mem dest.toNat 32 :=
  correctness z dest ret hret s0 setup hpre

end Witness

end Fv256.Arm64.WriteToArray32
