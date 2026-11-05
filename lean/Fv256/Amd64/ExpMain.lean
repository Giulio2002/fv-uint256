import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.ExpMath
import Fv256.ExpFinal
import Fv256.UtilF
import Fv256.Amd64.ExpSum
import Fv256.Amd64.ExpLoop1
import Fv256.Amd64.ExpLoop2
import Fv256.Amd64.ExpLoop3
import Fv256.Amd64.ExpLoop4
import Fv256.Amd64.EnsuresOfW
import Fv256.ExpPro
import Fv256.Amd64.ExpTac

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ExpMain

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem exp_summary :
    Summary Extracted.program Extracted.entry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x100 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x20 ∧ StackWritable s 0xa8 0x20 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 3).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 1).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 14).toNat + 16) ∧
        Extracted.program.DataLoaded s.mem)
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0xa8, (s.regs 4).toNat + 0x20)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hbw, hb⟩, ⟨hew, he⟩, hdz, hdb, hde, hdg, hdl⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdb hde hsp
  janus64_data hdl [hacc]
  janus64_run [Util.readLE_32] until [Extracted.entry + 0x149]
  · rename_i g1 e3z e2z e1z
    have hn0 : Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) < 2 ^ 20 := by
      have := Fv256.F.bitLen_le (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) 64 (Fv256.Util.readLE8_lt _ _)
      omega
    refine Fv256.Amd64.ExpLoop1.loop1 s _ (Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8)) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega) (by omega) hacc (min (Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8)) 64) 0 1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) _ (by omega) ?inv ?hex
    · unfold Fv256.Amd64.ExpLoop1.Inv1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, Fv256.Amd64.ExpLoop1.head1, Extracted.entry]
      · omega
      · decide
      · have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
        simpa using this
      · exact Fv256.Util.readLE8_lt _ _
      · exact Fv256.Util.readLE8_lt _ _
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.nbv0 _ (Fv256.Util.readLE8_lt _ _) _
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, setXmmF, hx15]
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 104 + 16 = BitVec.toNat (s.regs 4) - 88 := by omega
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        try simp
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 72 + 16 = BitVec.toNat (s.regs 4) - 56 := by omega
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 16; simpa using this),
          Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3) + 16) 16; simpa using this),
          ← Janus.Arm64.Memory.readLE_add]
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 0).isLt
        simp only [Nat.reducePow, Nat.reducePow] at this ⊢
        omega
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 1).isLt
        omega
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Fv256.F.nmem0 _ (Fv256.Util.readLE8_lt _ _) _
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := Fv256.Util.readLE8_lt s.mem (BitVec.toNat (s.regs 3))
        omega
      · rfl
      · rfl
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 5).isLt
        omega
      · janus_frame
    · intro S' hI
      obtain ⟨hpc, hk64, hr, hb, hw, hev, r3, r7, r8, r9, r0, r1, r2, r6, r4, r5, r14, x15', mr, mb, mz, mep, mn, mev, hdfS, hmxS, mbp, hfr⟩ := hI
      have hmin : min (Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8)) 64 = Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) := by
        have := Fv256.F.bitLen_le (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) 64 (Fv256.Util.readLE8_lt _ _)
        omega
      simp only [hmin] at r3 mr mb hr hb hw r8
      have hretS : Arm64.Memory.readLE S'.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
        rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hra2
      janus64_run [r3, r7, r8, r9, r0, r1, r2, r6, r4, r5, r14, mr, mb, mz, mep, mn, mev]
      refine ⟨?_, ?_⟩
      · rw [Fv256.F.copy32 S'.mem _ _ _ _ _ (by omega) (by omega) (by omega), mr,
          Fv256.F.exp_stage0 _ _ _ (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32; simpa using this) (Fv256.F.bitLen_lt _)]
        unfold Fv256.F.expSpec
        rw [Fv256.F.split4 s.mem (BitVec.toNat (s.regs 1)), e1z, e2z, e3z]
        simp
      · janus_frame
  · rename_i g1 e3z e2z e1z hev0
    have hn0 : Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) < 2 ^ 20 := by
      have := Fv256.F.bitLen_le (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) 64 (Fv256.Util.readLE8_lt _ _)
      omega
    refine Fv256.Amd64.ExpLoop1.loop1 s _ (Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8)) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega) (by omega) hacc (min (Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8)) 64) 0 1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) _ (by omega) ?inv_b ?hex_b
    · unfold Fv256.Amd64.ExpLoop1.Inv1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, Fv256.Amd64.ExpLoop1.head1, Extracted.entry]
      · omega
      · decide
      · have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
        simpa using this
      · exact Fv256.Util.readLE8_lt _ _
      · exact Fv256.Util.readLE8_lt _ _
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.nbv0 _ (Fv256.Util.readLE8_lt _ _) _
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, setXmmF, hx15]
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 104 + 16 = BitVec.toNat (s.regs 4) - 88 := by omega
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        try simp
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 72 + 16 = BitVec.toNat (s.regs 4) - 56 := by omega
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 16; simpa using this),
          Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3) + 16) 16; simpa using this),
          ← Janus.Arm64.Memory.readLE_add]
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 0).isLt
        simp only [Nat.reducePow, Nat.reducePow] at this ⊢
        omega
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 1).isLt
        omega
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Fv256.F.nmem0 _ (Fv256.Util.readLE8_lt _ _) _
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := Fv256.Util.readLE8_lt s.mem (BitVec.toNat (s.regs 3))
        omega
      · rfl
      · rfl
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 5).isLt
        omega
      · janus_frame
    · intro S' hI
      obtain ⟨hpc, hk64, hr, hb, hw, hev, r3, r7, r8, r9, r0, r1, r2, r6, r4, r5, r14, x15', mr, mb, mz, mep, mn, mev, hdfS, hmxS, mbp, hfr⟩ := hI
      have hmin : min (Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8)) 64 = Fv256.Spec.bitLen (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) := by
        have := Fv256.F.bitLen_le (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) 64 (Fv256.Util.readLE8_lt _ _)
        omega
      simp only [hmin] at r3 mr mb hr hb hw r8
      have hretS : Arm64.Memory.readLE S'.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
        rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hra2
      janus64_run [r3, r7, r8, r9, r0, r1, r2, r6, r4, r5, r14, mr, mb, mz, mep, mn, mev]
      refine ⟨?_, ?_⟩
      · rw [Fv256.F.copy32 S'.mem _ _ _ _ _ (by omega) (by omega) (by omega), mr,
          Fv256.F.exp_stage0 _ _ _ (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32; simpa using this) (Fv256.F.bitLen_lt _)]
        unfold Fv256.F.expSpec
        rw [Fv256.F.split4 s.mem (BitVec.toNat (s.regs 1)), e1z, e2z, e3z]
        simp
      · janus_frame
      · rename_i b1 b2 b3
        exfalso
        apply hev0
        simpa using b3
  · rename_i hg e3z e2z e1z hev hbl
    exact ⟨Fv256.F.early0 _ _ _ _ _ (Fv256.Util.readLE8_lt _ _) (Fv256.F.even_of_lsb _ hev) _ hbl, by janus_frame⟩
  · rename_i g1 e3z e2z e1nz
    have hcl := (Fv256.B.clz_norm (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) e1nz (Fv256.Util.readLE8_lt _ _)).1
    have hn0 : (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) < 2 ^ 20 := by omega_e
    refine Fv256.Amd64.ExpLoop1.loop1 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) 64) 0 1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) _ (by omega_e) ?inv1 ?hex1
    · unfold Fv256.Amd64.ExpLoop1.Inv1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, Fv256.Amd64.ExpLoop1.head1, Extracted.entry]
      · omega_e
      · decide
      · have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
        simpa using this
      · exact Fv256.Util.readLE8_lt _ _
      · exact Fv256.Util.readLE8_lt _ _
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.nbvk _ 65
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, setXmmF, hx15]
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 104 + 16 = BitVec.toNat (s.regs 4) - 88 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        try simp
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 72 + 16 = BitVec.toNat (s.regs 4) - 56 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 16; simpa using this),
          Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3) + 16) 16; simpa using this),
          ← Janus.Arm64.Memory.readLE_add]
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 0).isLt
        simp only [Nat.reducePow, Nat.reducePow] at this ⊢
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 1).isLt
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := Fv256.Util.readLE8_lt s.mem (BitVec.toNat (s.regs 3))
        omega_e
      · rfl
      · rfl
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 5).isLt
        omega_e
      · janus_frame
    · intro S1 hI1
      obtain ⟨hpc1, hk1, hr1, hb1, hw1, hev1, r31, r71, r81, r91, r01, r11, r21, r61, r41, r51, r141, x151, mr1, mb1, mz01, mep1, mn1, mev1, hdfS1, hmxS1, mbp1, hfr1⟩ := hI1
      have hmin1 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) 64 = 64 := by omega_e
      simp only [hmin1] at r31 mr1 mb1 hr1 hb1 hw1 r81
      have hretS1 : Arm64.Memory.readLE S1.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
        rw [hfr1.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
      janus64_run [r31, r71, r81, r91, r01, r11, r21, r61, r41, r51, r141, mr1, mb1, mz01, mep1, mn1, mev1] until [Extracted.entry + 0x1f4]
      refine Fv256.Amd64.ExpLoop2.loop2 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) 128 - 64) 64 (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1 (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) _ (by omega_e) ?inv2_1 ?hex2_1
      · unfold Fv256.Amd64.ExpLoop2.Inv2
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [setRegF, Fv256.Amd64.ExpLoop2.head2, Extracted.entry]
        · omega_e
        · exact hr1
        · exact hb1
        · exact Fv256.Util.readLE8_lt _ _
        · exact hev1
        · simp [setRegF, r31]
        · simp [setRegF, r71]
        · simp [setRegF]
        · simp [setRegF, r01]
        · simp [setRegF, r11]
        · simp [setRegF, r21]
        · simp [setRegF, r61]
        · simp [setRegF, r41]
        · simp [setRegF, r51]
        · simp [setRegF, r141]
        · simp [setRegF, x151]
        · exact mr1
        · exact mb1
        · exact mz01
        · exact mep1
        · exact mn1
        · exact mev1
        · rfl
        · rfl
        · exact mbp1
        · exact hfr1
      · intro S2 hI2
        obtain ⟨hpc2, hk2, hr2, hb2, hw2, hev2, r32, r72, r82, r02, r12, r22, r62, r42, r52, r142, x152, mr2, mb2, mz02, mep2, mn2, mev2, hdfS2, hmxS2, mbp2, hfr2⟩ := hI2
        have hmin2 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) 128 = (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) := by omega_e
        simp only [hmin2] at r32 mr2 mb2 hr2 hb2 hw2 r82
        have hretS2 : Arm64.Memory.readLE S2.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
          rw [hfr2.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
        janus64_run [r32, r72, r82, r02, r12, r22, r62, r42, r52, r142, mr2, mb2, mz02, mep2, mn2, mev2]
        refine ⟨?_, ?_⟩
        · rw [Fv256.F.copy32 S2.mem _ _ _ _ _ (by omega_e) (by omega_e) (by omega_e), mr2]
          unfold Fv256.F.expSpec
          have hBlt : (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) < Fv256.F.W := by
            have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
            simpa using this
          have hbl : Fv256.Spec.bitLen ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8)) = (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) := by
            have := Fv256.F.n_top1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e1nz
            exact this
          have he : ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8)) < 2 ^ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) := by
            have := Fv256.F.bitLen_lt ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))
            rw [hbl] at this
            exact this
          have hm := Fv256.F.exp_two (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 65) hBlt (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (by omega_e) (by omega_e) he
          simp only [Fv256.F.MEq] at hm
          rw [Nat.mod_eq_of_lt hr2] at hm
          have eE : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 32 = ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8)) := by
            rw [Fv256.F.split4 s.mem (BitVec.toNat (s.regs 1)), e2z, e3z]; omega_e
          rw [eE]
          exact hm
        · janus_frame
  · rename_i g1 e3z e2z e1nz hev0
    exact (Fv256.F.contra_big _ 65 (by decide) (by decide) (Fv256.Util.readLE8_lt _ _) hbr).elim
  · rename_i hg e3z e2z e1nz hev hbl
    exact ⟨Fv256.F.early1 _ _ _ _ _ _ (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e1nz (Fv256.F.even_of_lsb _ hev) hbl, by janus_frame⟩
  · rename_i g1 e3z e2nz
    have hcl := (Fv256.B.clz_norm (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) e2nz (Fv256.Util.readLE8_lt _ _)).1
    have hn0 : (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) < 2 ^ 20 := by omega_e
    refine Fv256.Amd64.ExpLoop1.loop1 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) 64) 0 1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) _ (by omega_e) ?inv2 ?hex2
    · unfold Fv256.Amd64.ExpLoop1.Inv1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, Fv256.Amd64.ExpLoop1.head1, Extracted.entry]
      · omega_e
      · decide
      · have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
        simpa using this
      · exact Fv256.Util.readLE8_lt _ _
      · exact Fv256.Util.readLE8_lt _ _
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.nbvk _ 129
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, setXmmF, hx15]
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 104 + 16 = BitVec.toNat (s.regs 4) - 88 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        try simp
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 72 + 16 = BitVec.toNat (s.regs 4) - 56 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 16; simpa using this),
          Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3) + 16) 16; simpa using this),
          ← Janus.Arm64.Memory.readLE_add]
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 0).isLt
        simp only [Nat.reducePow, Nat.reducePow] at this ⊢
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 1).isLt
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := Fv256.Util.readLE8_lt s.mem (BitVec.toNat (s.regs 3))
        omega_e
      · rfl
      · rfl
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 5).isLt
        omega_e
      · janus_frame
    · intro S1 hI1
      obtain ⟨hpc1, hk1, hr1, hb1, hw1, hev1, r31, r71, r81, r91, r01, r11, r21, r61, r41, r51, r141, x151, mr1, mb1, mz01, mep1, mn1, mev1, hdfS1, hmxS1, mbp1, hfr1⟩ := hI1
      have hmin1 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) 64 = 64 := by omega_e
      simp only [hmin1] at r31 mr1 mb1 hr1 hb1 hw1 r81
      have hretS1 : Arm64.Memory.readLE S1.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
        rw [hfr1.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
      janus64_run [r31, r71, r81, r91, r01, r11, r21, r61, r41, r51, r141, mr1, mb1, mz01, mep1, mn1, mev1] until [Extracted.entry + 0x1f4]
      refine Fv256.Amd64.ExpLoop2.loop2 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) 128 - 64) 64 (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1 (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) _ (by omega_e) ?inv2_2 ?hex2_2
      · unfold Fv256.Amd64.ExpLoop2.Inv2
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [setRegF, Fv256.Amd64.ExpLoop2.head2, Extracted.entry]
        · omega_e
        · exact hr1
        · exact hb1
        · exact Fv256.Util.readLE8_lt _ _
        · exact hev1
        · simp [setRegF, r31]
        · simp [setRegF, r71]
        · simp [setRegF]
        · simp [setRegF, r01]
        · simp [setRegF, r11]
        · simp [setRegF, r21]
        · simp [setRegF, r61]
        · simp [setRegF, r41]
        · simp [setRegF, r51]
        · simp [setRegF, r141]
        · simp [setRegF, x151]
        · exact mr1
        · exact mb1
        · exact mz01
        · exact mep1
        · exact mn1
        · exact mev1
        · rfl
        · rfl
        · exact mbp1
        · exact hfr1
      · intro S2 hI2
        obtain ⟨hpc2, hk2, hr2, hb2, hw2, hev2, r32, r72, r82, r02, r12, r22, r62, r42, r52, r142, x152, mr2, mb2, mz02, mep2, mn2, mev2, hdfS2, hmxS2, mbp2, hfr2⟩ := hI2
        have hmin2 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) 128 = 128 := by omega_e
        simp only [hmin2] at r32 mr2 mb2 hr2 hb2 hw2 r82
        have hretS2 : Arm64.Memory.readLE S2.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
          rw [hfr2.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
        janus64_run [r32, r72, r82, r02, r12, r22, r62, r42, r52, r142, mr2, mb2, mz02, mep2, mn2, mev2] until [Extracted.entry + 0x262]
        refine Fv256.Amd64.ExpLoop3.loop3 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) 192 - 128) 128 (Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).1 (Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).2.1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) _ (by omega_e) ?inv3_2 ?hex3_2
        · unfold Fv256.Amd64.ExpLoop3.Inv3
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [setRegF, Fv256.Amd64.ExpLoop3.head3, Extracted.entry]
          · omega_e
          · exact hr2
          · exact hb2
          · exact Fv256.Util.readLE8_lt _ _
          · exact hev2
          · simp [setRegF, r32]
          · simp [setRegF, r72]
          · simp [setRegF]
          · simp [setRegF, r02]
          · simp [setRegF, r12]
          · simp [setRegF, r22]
          · simp [setRegF, r62]
          · simp [setRegF, r42]
          · simp [setRegF, r52]
          · simp [setRegF, r142]
          · simp [setRegF, x152]
          · exact mr2
          · exact mb2
          · exact mz02
          · exact mep2
          · exact mn2
          · exact mev2
          · rfl
          · rfl
          · exact mbp2
          · exact hfr2
        · intro S3 hI3
          obtain ⟨hpc3, hk3, hr3, hb3, hw3, hev3, r33, r73, r83, r03, r13, r23, r63, r43, r53, r143, x153, mr3, mb3, mz03, mep3, mn3, mev3, hdfS3, hmxS3, mbp3, hfr3⟩ := hI3
          have hmin3 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) 192 = (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) := by omega_e
          simp only [hmin3] at r33 mr3 mb3 hr3 hb3 hw3 r83
          have hretS3 : Arm64.Memory.readLE S3.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
            rw [hfr3.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
          janus64_run [r33, r73, r83, r03, r13, r23, r63, r43, r53, r143, mr3, mb3, mz03, mep3, mn3, mev3]
          refine ⟨?_, ?_⟩
          · rw [Fv256.F.copy32 S3.mem _ _ _ _ _ (by omega_e) (by omega_e) (by omega_e), mr3]
            unfold Fv256.F.expSpec
            have hBlt : (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) < Fv256.F.W := by
              have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
              simpa using this
            have hbl : Fv256.Spec.bitLen ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8)) = (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) := by
              have := Fv256.F.n_top2 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e2nz
              exact this
            have he : ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8)) < 2 ^ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) := by
              have := Fv256.F.bitLen_lt ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8))
              rw [hbl] at this
              exact this
            have hm := Fv256.F.exp_three (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 129) hBlt (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (by omega_e) (by omega_e) he
            simp only [Fv256.F.MEq] at hm
            rw [Nat.mod_eq_of_lt hr3] at hm
            have eE : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 32 = ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8)) := by
              rw [Fv256.F.split4 s.mem (BitVec.toNat (s.regs 1)), e3z]; omega_e
            rw [eE]
            exact hm
          · janus_frame
  · rename_i g1 e3z e2nz hev0
    exact (Fv256.F.contra_big _ 129 (by decide) (by decide) (Fv256.Util.readLE8_lt _ _) hbr).elim
  · rename_i hg e3z e2nz hev hbl
    exact ⟨Fv256.F.early2 _ _ _ _ _ _ _ (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e2nz (Fv256.F.even_of_lsb _ hev) hbl, by janus_frame⟩
  · rename_i g1 e3nz
    have hcl := (Fv256.B.clz_norm (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) e3nz (Fv256.Util.readLE8_lt _ _)).1
    have hn0 : (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) < 2 ^ 20 := by omega_e
    refine Fv256.Amd64.ExpLoop1.loop1 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 64) 0 1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) _ (by omega_e) ?inv3 ?hex3
    · unfold Fv256.Amd64.ExpLoop1.Inv1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, Fv256.Amd64.ExpLoop1.head1, Extracted.entry]
      · omega_e
      · decide
      · have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
        simpa using this
      · exact Fv256.Util.readLE8_lt _ _
      · exact Fv256.Util.readLE8_lt _ _
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.nbvk _ 193
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, setXmmF, hx15]
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 104 + 16 = BitVec.toNat (s.regs 4) - 88 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        try simp
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 72 + 16 = BitVec.toNat (s.regs 4) - 56 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 16; simpa using this),
          Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3) + 16) 16; simpa using this),
          ← Janus.Arm64.Memory.readLE_add]
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 0).isLt
        simp only [Nat.reducePow, Nat.reducePow] at this ⊢
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 1).isLt
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := Fv256.Util.readLE8_lt s.mem (BitVec.toNat (s.regs 3))
        omega_e
      · rfl
      · rfl
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 5).isLt
        omega_e
      · janus_frame
    · intro S1 hI1
      obtain ⟨hpc1, hk1, hr1, hb1, hw1, hev1, r31, r71, r81, r91, r01, r11, r21, r61, r41, r51, r141, x151, mr1, mb1, mz01, mep1, mn1, mev1, hdfS1, hmxS1, mbp1, hfr1⟩ := hI1
      have hmin1 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 64 = 64 := by omega_e
      simp only [hmin1] at r31 mr1 mb1 hr1 hb1 hw1 r81
      have hretS1 : Arm64.Memory.readLE S1.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
        rw [hfr1.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
      janus64_run [r31, r71, r81, r91, r01, r11, r21, r61, r41, r51, r141, mr1, mb1, mz01, mep1, mn1, mev1] until [Extracted.entry + 0x1f4]
      refine Fv256.Amd64.ExpLoop2.loop2 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 128 - 64) 64 (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1 (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) _ (by omega_e) ?inv2_3 ?hex2_3
      · unfold Fv256.Amd64.ExpLoop2.Inv2
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [setRegF, Fv256.Amd64.ExpLoop2.head2, Extracted.entry]
        · omega_e
        · exact hr1
        · exact hb1
        · exact Fv256.Util.readLE8_lt _ _
        · exact hev1
        · simp [setRegF, r31]
        · simp [setRegF, r71]
        · simp [setRegF]
        · simp [setRegF, r01]
        · simp [setRegF, r11]
        · simp [setRegF, r21]
        · simp [setRegF, r61]
        · simp [setRegF, r41]
        · simp [setRegF, r51]
        · simp [setRegF, r141]
        · simp [setRegF, x151]
        · exact mr1
        · exact mb1
        · exact mz01
        · exact mep1
        · exact mn1
        · exact mev1
        · rfl
        · rfl
        · exact mbp1
        · exact hfr1
      · intro S2 hI2
        obtain ⟨hpc2, hk2, hr2, hb2, hw2, hev2, r32, r72, r82, r02, r12, r22, r62, r42, r52, r142, x152, mr2, mb2, mz02, mep2, mn2, mev2, hdfS2, hmxS2, mbp2, hfr2⟩ := hI2
        have hmin2 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 128 = 128 := by omega_e
        simp only [hmin2] at r32 mr2 mb2 hr2 hb2 hw2 r82
        have hretS2 : Arm64.Memory.readLE S2.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
          rw [hfr2.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
        janus64_run [r32, r72, r82, r02, r12, r22, r62, r42, r52, r142, mr2, mb2, mz02, mep2, mn2, mev2] until [Extracted.entry + 0x262]
        refine Fv256.Amd64.ExpLoop3.loop3 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 192 - 128) 128 (Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).1 (Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).2.1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) _ (by omega_e) ?inv3_3 ?hex3_3
        · unfold Fv256.Amd64.ExpLoop3.Inv3
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [setRegF, Fv256.Amd64.ExpLoop3.head3, Extracted.entry]
          · omega_e
          · exact hr2
          · exact hb2
          · exact Fv256.Util.readLE8_lt _ _
          · exact hev2
          · simp [setRegF, r32]
          · simp [setRegF, r72]
          · simp [setRegF]
          · simp [setRegF, r02]
          · simp [setRegF, r12]
          · simp [setRegF, r22]
          · simp [setRegF, r62]
          · simp [setRegF, r42]
          · simp [setRegF, r52]
          · simp [setRegF, r142]
          · simp [setRegF, x152]
          · exact mr2
          · exact mb2
          · exact mz02
          · exact mep2
          · exact mn2
          · exact mev2
          · rfl
          · rfl
          · exact mbp2
          · exact hfr2
        · intro S3 hI3
          obtain ⟨hpc3, hk3, hr3, hb3, hw3, hev3, r33, r73, r83, r03, r13, r23, r63, r43, r53, r143, x153, mr3, mb3, mz03, mep3, mn3, mev3, hdfS3, hmxS3, mbp3, hfr3⟩ := hI3
          have hmin3 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 192 = 192 := by omega_e
          simp only [hmin3] at r33 mr3 mb3 hr3 hb3 hw3 r83
          have hretS3 : Arm64.Memory.readLE S3.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
            rw [hfr3.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
          janus64_run [r33, r73, r83, r03, r13, r23, r63, r43, r53, r143, mr3, mb3, mz03, mep3, mn3, mev3] until [Extracted.entry + 0x2cc]
          refine Fv256.Amd64.ExpLoop4.loop4 s _ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) (BitVec.toNat (s.regs 0)) (BitVec.toNat (s.regs 1)) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8) hn0 (by omega_e) hnw hacc (min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 256 - 192) 192 (Fv256.F.expIter 64 ((Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).1, (Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8))).1 (Fv256.F.expIter 64 ((Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).1, (Fv256.F.expIter 64 ((Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).1, (Fv256.F.expIter 64 (1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32), (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8))).2.1, (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8))).2.1 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) _ (by omega_e) ?inv4_3 ?hex4_3
          · unfold Fv256.Amd64.ExpLoop4.Inv4
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [setRegF, Fv256.Amd64.ExpLoop4.head4, Extracted.entry]
            · omega_e
            · exact hr3
            · exact hb3
            · exact Fv256.Util.readLE8_lt _ _
            · exact hev3
            · simp [setRegF, r33]
            · simp [setRegF, r73]
            · simp [setRegF]
            · simp [setRegF, r03]
            · simp [setRegF, r23]
            · simp [setRegF, r63]
            · simp [setRegF, r43]
            · simp [setRegF, r53]
            · simp [setRegF, r143]
            · simp [setRegF, x153]
            · exact mr3
            · exact mb3
            · exact mz03
            · exact mep3
            · exact mn3
            · exact mev3
            · rfl
            · rfl
            · exact mbp3
            · exact hfr3
          · intro S4 hI4
            obtain ⟨hpc4, hk4, hr4, hb4, hw4, hev4, r34, r74, r84, r04, r24, r64, r44, r54, r144, x154, mr4, mb4, mz04, mep4, mn4, mev4, hdfS4, hmxS4, mbp4, hfr4⟩ := hI4
            have hmin4 : min (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 256 = (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) := by omega_e
            simp only [hmin4] at r34 mr4 mb4 hr4 hb4 hw4 r84
            have hretS4 : Arm64.Memory.readLE S4.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
              rw [hfr4.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
            janus64_run [r34, r74, r84, r04, r24, r64, r44, r54, r144, mr4, mb4, mz04, mep4, mn4, mev4]
            refine ⟨?_, ?_⟩
            · rw [Fv256.F.copy32 S4.mem _ _ _ _ _ (by omega_e) (by omega_e) (by omega_e), mr4]
              unfold Fv256.F.expSpec
              have hBlt : (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) < Fv256.F.W := by
                have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
                simpa using this
              have hbl : Fv256.Spec.bitLen ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 2 ^ 192 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8)) = (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) := by
                have := Fv256.F.n_top3 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e3nz
                exact this
              have he : ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 2 ^ 192 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8)) < 2 ^ (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) := by
                have := Fv256.F.bitLen_lt ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 2 ^ 192 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8))
                rw [hbl] at this
                exact this
              have hm := Fv256.F.exp_four (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) (63 - Janus.Arm64.clzNat 64 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8) + 193) 64 rfl hBlt (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (by omega_e) (by omega_e) he
              simp only [Fv256.F.MEq] at hm
              rw [Nat.mod_eq_of_lt hr4] at hm
              have eE : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 32 = ((Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) + 2 ^ 64 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) + 2 ^ 128 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8) + 2 ^ 192 * (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8)) := by
                rw [Fv256.F.split4 s.mem (BitVec.toNat (s.regs 1))]; omega_e
              rw [eE]
              exact hm
            · janus_frame
  · rename_i g1 e3nz hev0
    exact (Fv256.F.contra_big _ 193 (by decide) (by decide) (Fv256.Util.readLE8_lt _ _) hbr).elim
  · rename_i hg e3nz hev hbl
    exact ⟨Fv256.F.early3 _ _ _ _ _ _ _ _ (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e3nz (Fv256.F.even_of_lsb _ hev) hbl, by janus_frame⟩

theorem correctness (z b e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b, e]
      (fun s => StackGuardOK s 0x20 ∧ 0x100 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xa8 0x20 ∧ Buffer s z 32 true ∧
        Buffer s b 32 false ∧ Buffer s e 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ z.toNat) ∧
        (b.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ b.toNat) ∧
        (e.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ e.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ (s.regs regG).toNat + 16) ∧
        Extracted.program.DataLoaded s.mem)
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.F.expSpec (valueAt s b 32) (valueAt s e 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xa8, (s.regs regSP).toNat + 0x20)]) :=
  Fv256.Amd64.EnsuresOfW.ensures3w 0x100 0xa8 0x20 0x20 (by decide) (by decide) Fv256.F.expSpec exp_summary z b e

end Fv256.Amd64.ExpMain
