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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        simp
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
      · janus_frame
    · sorry
  · sorry
  · rename_i hg e3z e2z e1z hev hbl
    exact ⟨Fv256.F.early0 _ _ _ _ _ (Fv256.Util.readLE8_lt _ _) (Fv256.F.even_of_lsb _ hev) _ hbl, by janus_frame⟩
  · sorry
  · sorry
  · rename_i hg e3z e2z e1nz hev hbl
    exact ⟨Fv256.F.early1 _ _ _ _ _ _ (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e1nz (Fv256.F.even_of_lsb _ hev) hbl, by janus_frame⟩
  · sorry
  · sorry
  · rename_i hg e3z e2nz hev hbl
    exact ⟨Fv256.F.early2 _ _ _ _ _ _ _ (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) e2nz (Fv256.F.even_of_lsb _ hev) hbl, by janus_frame⟩
  · sorry
  · sorry
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
