import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).WriteToArray20(dest *[32]byte)` (amd64)

**Guarantee.** For all pointers `z` (the receiver, `RAX`) and `dest` (`RBX`) such that the return-address slot is writable, the
32 bytes at `z` are readable, the 20 bytes at `dest` are writable (below `2^48`) and the two ranges are disjoint, the call
returns (no fault, no panic), obeys the ABI, the 20 bytes at `dest` afterwards read as the big-endian number
`Fv256.Spec.fromBE` equal to the number at `z` modulo `2^160` (read before the call), and no byte changes outside `dest[0..20)`.
(The compiled code interleaves its loads and stores, so overlapping `z` and `dest` is outside the guarantee.)

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToArray20

set_option maxHeartbeats 8000000 in
theorem correctness (z dest : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, dest]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s dest 20 true ∧
        (z.toNat + 32 ≤ dest.toNat ∨ dest.toNat + 20 ≤ z.toNat) ∧
        (dest.toNat + 20 ≤ (s.regs regSP).toNat ∨ (s.regs regSP).toNat + 8 ≤ dest.toNat))
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (dest.toNat + i) 1) 20 = valueAt s z 32 % 2 ^ 160 ∧
        Janus.Spec.OnlyWrites s.mem s'.mem dest.toNat 20) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hdw, hd⟩, hdis, hds⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · rw [Util.be20_rev]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    have h4 := Util.revBytes_lt 4 (s.mem.readLE (z.toNat + 16) 8 % 4294967296)
    have h1 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 8) 8)
    have h0 := Util.revBytes_lt 8 (s.mem.readLE z.toNat 8)
    simp only [Nat.reducePow] at h4 h1 h0
    rw [Nat.mod_mod, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h0,
      Util.rev4_rev4 _ (Nat.mod_lt _ (by decide)), Util.rev8_rev8 _ (Util.readLE8_lt _ _), Util.rev8_rev8 _ (Util.readLE8_lt _ _)]
    have := Util.readLE8_lt s.mem z.toNat
    have := Util.readLE8_lt s.mem (z.toNat + 8)
    have := Util.readLE8_lt s.mem (z.toNat + 16)
    have := Util.readLE8_lt s.mem (z.toNat + 24)
    omega
  · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def dest : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then dest else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dest] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 false ∧ Buffer s0 dest 20 true ∧
    (z.toNat + 32 ≤ dest.toNat ∨ dest.toNat + 20 ≤ z.toNat) ∧
    (dest.toNat + 20 ≤ (s0.regs regSP).toNat ∨ (s0.regs regSP).toNat + 8 ≤ dest.toNat) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z dest : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dest] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s dest 20 true ∧
      (z.toNat + 32 ≤ dest.toNat ∨ dest.toNat + 20 ≤ z.toNat) ∧
      (dest.toNat + 20 ≤ (s.regs regSP).toNat ∨ (s.regs regSP).toNat + 8 ≤ dest.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Spec.fromBE (fun i => s'.mem.readLE (dest.toNat + i) 1) 20 = valueAt s z 32 % 2 ^ 160 ∧
        Janus.Spec.OnlyWrites s.mem s'.mem dest.toNat 20 :=
  ⟨ret, s0, z, dest, hret, setup, hpre,
    correctness z dest ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Fv256.Spec.fromBE (fun i => s'.mem.readLE (dest.toNat + i) 1) 20 = valueAt s0 z 32 % 2 ^ 160 ∧
      Janus.Spec.OnlyWrites s0.mem s'.mem dest.toNat 20 :=
  correctness z dest ret hret s0 setup hpre

end Witness

end Fv256.Amd64.WriteToArray20
