import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).HashTreeRoot() ([32]byte, error)` (amd64)

The 32 result bytes are returned in the caller's frame at `RSP+8`; the compiled code copies a local 32-byte array with a call to
`runtime.memmove` (its assembly is part of the extracted program; for the constant size 32 it takes the straight-line SSE path).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.HashTreeRoot

set_option maxHeartbeats 8000000 in
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 112 40 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 112 ∨ (s.regs regSP).toNat + 40 ≤ z.toNat))
      (fun s s' => s'.mem.readLE ((s.regs regSP).toNat + 8) 32 = valueAt s z 32 ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧
        Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 32 ((s.regs regSP).toNat - 112) 112) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, hds⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hds
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · simp only [Nat.add_assoc, Nat.reduceAdd]
    simp (disch := omega) only [Util.rd16, Util.w16_lo, Util.w16_hi, Util.readLE_writeLE_eq, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have h0 := Util.readLE8_lt s.mem z.toNat
    have h1 := Util.readLE8_lt s.mem (z.toNat + 8)
    have h2 := Util.readLE8_lt s.mem (z.toNat + 16)
    have h3 := Util.readLE8_lt s.mem (z.toNat + 24)
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.reducePow, Util.readLE8_mod]
    omega
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 112 40 ∧ Buffer s0 z 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 112 ∨ (s0.regs regSP).toNat + 40 ≤ z.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 112 40 ∧ Buffer s z 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 112 ∨ (s.regs regSP).toNat + 40 ≤ z.toNat)) :=
  ⟨ret, s0, z, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.mem.readLE ((s0.regs regSP).toNat + 8) 32 = valueAt s0 z 32 ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem ((s0.regs regSP).toNat + 8) 32 ((s0.regs regSP).toNat - 112) 112 := by
  refine (correctness z ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end Witness

end Fv256.Amd64.HashTreeRoot
