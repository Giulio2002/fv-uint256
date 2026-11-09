import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).Bytes32() [32]byte` (amd64)

**Guarantee.** For every receiver `z` (`RAX`) and every Go call such that the return-address slot and the frame window
`[RSP-40, RSP+40)` (the saved frame pointer, a local copy of the array, and the 32 result bytes the callee returns in the caller's
frame at `RSP+8`) are writable, the 32 bytes at `z` are readable (below `2^48`) and do not overlap that window: the call returns
(no fault, no panic), obeys the ABI, the 32 result bytes at `RSP+8` read as the big-endian number (`Fv256.Spec.fromBE`) equal to the
number at `z` (read before the call), and no byte changes outside the result bytes and the frame window (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Bytes32

set_option maxHeartbeats 8000000 in
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => StackWritable s 40 40 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 40 ≤ z.toNat))
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) 32 = valueAt s z 32 ∧
        Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 32 ((s.regs regSP).toNat - 40) 40) := by
  intro ret hret s hs ⟨⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, hds⟩
  janus64_intro hs
  simp only [regSP] at hacc hlow hnw hds
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · rw [Util.be32_rev]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    simp (disch := omega) only [Util.rd16, Util.w16_lo, Util.w16_hi, Util.readLE_writeLE_eq, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    simp only [Nat.reducePow]
    have h0 := Util.revBytes_lt 8 (s.mem.readLE z.toNat 8)
    have h1 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 8) 8)
    have h2 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 16) 8)
    have h3 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 24) 8)
    simp only [Nat.reducePow] at h0 h1 h2 h3
    rw [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3,
      Util.lo16 _ _ h3, Util.hi16 _ _ h3 h2, Util.lo16 _ _ h1, Util.hi16 _ _ h1 h0,
      Util.rev8_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _),
      Util.rev8_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _)]
    have := Util.readLE8_lt s.mem z.toNat
    have := Util.readLE8_lt s.mem (z.toNat + 8)
    have := Util.readLE8_lt s.mem (z.toNat + 16)
    have := Util.readLE8_lt s.mem (z.toNat + 24)
    omega
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackWritable s0 40 40 ∧ Buffer s0 z 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 40 ≤ z.toNat) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧
    (StackWritable s 40 40 ∧ Buffer s z 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 40 ≤ z.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Spec.fromBE (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) 32 = valueAt s z 32 ∧
        Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 32 ((s.regs regSP).toNat - 40) 40 :=
  ⟨ret, s0, z, hret, setup, hpre,
    correctness z ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧
      Fv256.Spec.fromBE (fun i => s'.mem.readLE ((s0.regs regSP).toNat + 8 + i) 1) 32 = valueAt s0 z 32 ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem ((s0.regs regSP).toNat + 8) 32 ((s0.regs regSP).toNat - 40) 40 :=
  correctness z ret hret s0 setup hpre

end Witness

end Fv256.Amd64.Bytes32
