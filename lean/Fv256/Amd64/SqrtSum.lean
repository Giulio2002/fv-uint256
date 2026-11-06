import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.SqrtMath
import Fv256.SqrtHead
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.SqrtSmall

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

/-- precondition of the `Sqrt` summary (receiver `RAX`, operand `RBX`; return address at `[RSP]`) -/
abbrev SPre (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  0x280 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x200 ∧ StackWritable s 0x1f0 0x18 ∧ s.xmm 15 = 0 ∧
  Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧
  ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0x1f0 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 0).toNat) ∧
  ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0x1f0 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 3).toNat) ∧
  (s.regs 0 = s.regs 3 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 32 ≤ (s.regs 0).toNat) ∧
  ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x1f0 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 14).toNat + 16)

abbrev SPost (s s' : State) : Prop :=
  s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
  Fv256.F.IsSqrt (s.mem.readLE (s.regs 3).toNat 32) (s'.mem.readLE (s.regs 0).toNat 32) ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem sqrt_small :
    Summary Extracted.program Extracted.entry
      (fun s => SPre s ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧
        s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0)
      SPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hzx, hdg⟩, h1, h2, h3⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  janus64_run [Util.readLE_32, Fv256.B.or3_zero_iff, h1, h2, h3] until [headS]
  · have hx32 : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 := by
      rw [Util.readLE_32, h1, h2, h3]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp
    · simp
    · rw [hx32]
      simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
      have hlt : s.mem.readLE (s.regs 3).toNat 8 < 256 ^ 8 := by
        have : (2 : Nat) < 256 ^ 8 := by decide
        omega
      rw [Nat.mod_eq_of_lt hlt]
      simp only [Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
      unfold Fv256.F.IsSqrt
      generalize s.mem.readLE (s.regs 3).toNat 8 = x0 at *
      rcases (by omega : x0 = 0 ∨ x0 = 1) with rfl | rfl <;> decide
    · janus_frame
  · exfalso
    rename_i hcl0 hcl
    have hxn : s.mem.readLE (s.regs 3).toNat 8 ≠ 0 := by omega
    simp only [if_neg hxn] at hcl
    exact SqrtHead.cl_ne_zero _ (by omega) (Util.readLE8_lt s.mem (s.regs 3).toNat) hcl
  · have hx32 : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 := by
      rw [Util.readLE_32, h1, h2, h3]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp
    · simp
    · rw [hx32]
      simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
      have hlt : s.mem.readLE (s.regs 3).toNat 8 < 256 ^ 8 := by
        have : (2 : Nat) < 256 ^ 8 := by decide
        omega
      rw [Nat.mod_eq_of_lt hlt]
      simp only [Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
      unfold Fv256.F.IsSqrt
      generalize s.mem.readLE (s.regs 3).toNat 8 = x0 at *
      rcases (by omega : x0 = 0 ∨ x0 = 1) with rfl | rfl <;> decide
    · janus_frame
  · rename_i hb0 hbcl
    have hx2 : 2 ≤ s.mem.readLE (s.regs 3).toNat 8 := by omega
    have hx64 := Util.readLE8_lt s.mem (s.regs 3).toNat
    have hxn : s.mem.readLE (s.regs 3).toNat 8 ≠ 0 := by omega
    simp only [if_neg hxn] at hbcl ⊢
    have hcl := SqrtHead.cl_val _ hx2 hx64
    have hrg := SqrtHead.cl_range _ hx2 hx64
    have hmod : ((BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 (s.mem.readLE (s.regs 3).toNat 8)) + 2#64) >>> 1).toNat % 64
        = (Spec.bitLen (s.mem.readLE (s.regs 3).toNat 8) + 1) / 2 := by
      rw [hcl]; exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have hr3 : (1#64 <<< ((Spec.bitLen (s.mem.readLE (s.regs 3).toNat 8) + 1) / 2)) =
        BitVec.ofNat 64 (2 ^ ((Spec.bitLen (s.mem.readLE (s.regs 3).toNat 8) + 1) / 2)) := by
      apply BitVec.eq_of_toNat_eq
      rw [SqrtHead.shl_val _ (by omega), BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 32)) (by decide))).symm
    rw [hr3]
    have hx32 : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 := by
      rw [Util.readLE_32, h1, h2, h3]; simp
    refine small_loop s (s.mem.readLE (s.regs 3).toNat 8) (s.regs 0) (SPost s) (by omega) (by omega) hra2 (2 ^ ((Spec.bitLen (s.mem.readLE (s.regs 3).toNat 8) + 1) / 2)) _ ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.two_pow_pos _, ?_, hx2, hx64, SqrtHead.init_inv _ hx2 hx64, ?_, hzw, ?_, ?_, ?_, ?_⟩
      · simp [Extracted.entry, headS]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, hx15]
      · simp
      · simp
      · exact Nat.pow_le_pow_right (by omega) (by omega)
      · simp [hz]
      · simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact Janus.Arm64.Memory.accessible_sub s.mem hacc (Or.inl rfl) (by omega) (by omega)
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; omega)
      · omega
      · exact (MemFrame.refl _ _).writeLE_inRanges _ ⟨((s.regs 4).toNat - 8, (s.regs 4).toNat), by simp, by omega, by omega⟩
    · intro r S' hsq h0 h4 h5 h14 hx15' hdf' hmx' hr hfr'
      refine ⟨h0, h4, h5, h14, ?_, hdf', hmx', ?_, ?_⟩
      · rw [hx15', hx15]
      · rw [hr, hx32]; exact hsq
      · refine hfr'.mono ?_
        intro a n h
        simp [Outside] at h ⊢
        omega

end Fv256.Amd64.Sqrt
