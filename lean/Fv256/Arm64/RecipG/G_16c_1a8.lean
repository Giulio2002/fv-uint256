import Fv256.Arm64.RecipLive

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def P_16c_1a8 (s : State) (x16cr0 x16cr2 x16cr3 x16cr4 x16cr5 x16cr7 x16cr10 x16cm176 x16cm240 x16cm248 x16cm256 : Nat) (S' : State) : Prop :=
  ∃ x1a8r1 x1a8r8 x1a8r9 x1a8r11 x1a8r14 x1a8r15, L1a8 S' x16cr0 x1a8r1 x16cr2 x16cr3 x16cr4 x16cr5 x16cr7 x1a8r8 x1a8r9 x16cr10 x1a8r11 x1a8r14 x1a8r15 x16cm176 x16cm240 x16cm248 x16cm256 ∧ x1a8r1 = (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr3) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7 * BitVec.ofNat 64 x16cr7))).toNat ∧ x1a8r8 = (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7 + BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7)) + BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7).toNat ∧ x1a8r9 = ((addWithCarry (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr0) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) false).snd.c).fst (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7 + BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) false).snd.c).fst).toNat ∧ x1a8r11 = ((addWithCarry (addWithCarry (BitVec.ofNat 64 x16cr10) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr0) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) false).snd.c).snd.c).fst (BitVec.ofNat 64 x16cr10) (addWithCarry (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr0) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) false).snd.c).fst (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7 + BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) false).snd.c).snd.c).fst).toNat ∧ x1a8r14 = (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr2) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7 * BitVec.ofNat 64 x16cr7))).toNat ∧ x1a8r15 = (BitVec.ofNat 64 x16cr3 * (BitVec.ofNat 64 x16cr7 * BitVec.ofNat 64 x16cr7)).toNat ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_16c_1a8 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0x16c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (x16cr0 x16cr2 x16cr3 x16cr4 x16cr5 x16cr7 x16cr10 x16cm176 x16cm240 x16cm248 x16cm256 : Nat) (hL : L16c S x16cr0 x16cr2 x16cr3 x16cr4 x16cr5 x16cr7 x16cr10 x16cm176 x16cm240 x16cm248 x16cm256) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1a8)) S (P_16c_1a8 s x16cr0 x16cr2 x16cr3 x16cr4 x16cr5 x16cr7 x16cr10 x16cm176 x16cm240 x16cm248 x16cm256) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 328 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 280 by omega]; exact hsd
  obtain ⟨hE_x16cr0, hB_x16cr0, hE_x16cr2, hB_x16cr2, hE_x16cr3, hB_x16cr3, hE_x16cr4, hB_x16cr4, hE_x16cr5, hB_x16cr5, hE_x16cr7, hB_x16cr7, hE_x16cr10, hB_x16cr10, hE_x16cm176, hB_x16cm176, hE_x16cm240, hB_x16cm240, hE_x16cm248, hB_x16cm248, hE_x16cm256, hB_x16cm256⟩ := hL
  janus_run [hE_x16cr0, hE_x16cr2, hE_x16cr3, hE_x16cr4, hE_x16cr5, hE_x16cr7, hE_x16cr10, hE_x16cm176, hE_x16cm240, hE_x16cm248, hE_x16cm256, Nat.mod_eq_of_lt hB_x16cr0, Nat.mod_eq_of_lt hB_x16cr2, Nat.mod_eq_of_lt hB_x16cr3, Nat.mod_eq_of_lt hB_x16cr4, Nat.mod_eq_of_lt hB_x16cr5, Nat.mod_eq_of_lt hB_x16cr7, Nat.mod_eq_of_lt hB_x16cr10, Nat.mod_eq_of_lt hB_x16cm176, Nat.mod_eq_of_lt hB_x16cm240, Nat.mod_eq_of_lt hB_x16cm248, Nat.mod_eq_of_lt hB_x16cm256, Fv256.B.rot32_and, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [recEntry + 0x1a8]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  unfold P_16c_1a8
  refine ⟨(BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr3) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7 * BitVec.ofNat 64 x16cr7))).toNat, (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7 + BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7)) + BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7).toNat, ((addWithCarry (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr0) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) false).snd.c).fst (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7 + BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) false).snd.c).fst).toNat, ((addWithCarry (addWithCarry (BitVec.ofNat 64 x16cr10) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr0) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) false).snd.c).snd.c).fst (BitVec.ofNat 64 x16cr10) (addWithCarry (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr0) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) false).snd.c).fst (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr0) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (addWithCarry (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7 + BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7))) (BitVec.ofNat 64 x16cr0 * BitVec.ofNat 64 x16cr7) false).snd.c).snd.c).fst).toNat, (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x16cr2) * BitVec.setWidth 128 (BitVec.ofNat 64 x16cr7 * BitVec.ofNat 64 x16cr7))).toNat, (BitVec.ofNat 64 x16cr3 * (BitVec.ofNat 64 x16cr7 * BitVec.ofNat 64 x16cr7)).toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L1a8
    and_intros
    · first | exact hE_x16cr0 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x16cr0)
    · exact hB_x16cr0
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x16cr2 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x16cr2)
    · exact hB_x16cr2
    · first | exact hE_x16cr3 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x16cr3)
    · exact hB_x16cr3
    · first | exact hE_x16cr4 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x16cr4)
    · exact hB_x16cr4
    · first | exact hE_x16cr5 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x16cr5)
    · exact hB_x16cr5
    · first | exact hE_x16cr7 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x16cr7)
    · exact hB_x16cr7
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x16cr10 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x16cr10)
    · exact hB_x16cr10
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x16cm176 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x16cm176)
    · exact hB_x16cm176
    · first | exact hE_x16cm240 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x16cm240)
    · exact hB_x16cm240
    · first | exact hE_x16cm248 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x16cm248)
    · exact hB_x16cm248
    · first | exact hE_x16cm256 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x16cm256)
    · exact hB_x16cm256
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · refine ⟨hR.1, ?_, ?_⟩
    · first | exact hR.2.1 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.1)
    · first | exact hR.2.2 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.2)
  · dsimp only
    repeat (refine RecMem.write ?_ _ _ _ (by omega) (by omega) (by omega) hsb)
    exact hM
  )

end Fv256.Arm64.RecipSeg
