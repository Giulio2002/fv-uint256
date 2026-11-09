import Fv256.Proofs.Arm64.ErlpDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

/-- the join invariant from the facts the symbolic execution of the prefix gives -/
theorem ej_of {s S : State} {z tab w : BitVec 64} {ret bl : Nat}
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x88)) (h0 : S.regs 0 = z) (h3 : S.regs 3 = BitVec.ofNat 64 bl)
    (hsp : S.sp = s.sp - 64#64) (h29 : S.regs 29 = s.sp - 72#64) (h28 : S.regs 28 = s.regs 28)
    (h18 : S.regs 18 = s.regs 18)
    (hmem : S.mem = (((s.mem.writeLE (s.sp.toNat - 64) 8 ret).writeLE (s.sp.toNat - 72) 8 (s.regs 29).toNat).writeLE
      (s.sp.toNat + 24) 8 w.toNat).writeLE (s.sp.toNat + 16) 8 tab.toNat)
    (hret : ret < 2 ^ 64) (hrsp : 72 ≤ s.sp.toNat) (hrsp2 : s.sp.toNat + 32 ≤ 2 ^ 48) :
    EJ z tab w ret s S bl := by
  refine ⟨hpc, h0, h3, hsp, h29, h28, h18, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem]
    refine ⟨fun a n h => ?_, fun a n b => ?_⟩
    · simp only [outside_cons, outside_nil] at h
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp only [Janus.Arm64.Memory.accessible_writeLE]
  · rw [hmem]; rfl
  · rw [hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have : tab.toNat < 2 ^ 64 := tab.isLt
    omega
  · rw [hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have : w.toNat < 2 ^ 64 := w.isLt
    omega
  · rw [hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have : (s.regs 29).toNat < 2 ^ 64 := (s.regs 29).isLt
    omega
  · rw [hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    omega

end Fv256.Arm64.EncodeRLP
