import Fv256.Proofs.Amd64.ErlpDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

/-- the join invariant from the facts the symbolic execution of the prefix gives -/
theorem ej_of {s S : State} {z tab w : BitVec 64} {bl : Nat}
    (hrip : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xa0)) (h0 : S.regs 0 = z) (h2 : S.regs 2 = BitVec.ofNat 64 bl)
    (h4 : S.regs 4 = s.regs 4 - 48#64) (h5 : S.regs 5 = s.regs 4 - 8#64) (h14 : S.regs 14 = s.regs 14)
    (hx : S.xmm = s.xmm) (hdf : S.df = s.df)
    (hmem : S.mem = ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 24) 8 w.toNat).writeLE
      ((s.regs 4).toNat + 16) 8 tab.toNat)
    (hrsp : 8 ≤ (s.regs 4).toNat) (hrsp2 : (s.regs 4).toNat + 32 ≤ 2 ^ 48) :
    EJ z tab w s S bl := by
  refine ⟨hrip, h0, h2, h4, h5, h14, hx, hdf, ?_, ?_, ?_, ?_, ?_⟩
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
    have : (s.regs 5).toNat < 2 ^ 64 := (s.regs 5).isLt
    omega

end Fv256.Amd64.EncodeRLP
