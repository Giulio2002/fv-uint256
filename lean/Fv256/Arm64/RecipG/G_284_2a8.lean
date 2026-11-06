import Fv256.Arm64.RecipLive

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def P_284_2a8 (s : State) (x284r0 x284r1 x284r2 x284r3 x284r10 x284m128 x284m136 x284m176 x284m240 x284m248 x284m256 : Nat) (S' : State) : Prop :=
  ∃ x2a8r4 x2a8r5 x2a8r6 x2a8r7 x2a8r8 x2a8r9 x2a8r11 x2a8r12 x2a8m144, L2a8 S' x284r0 x284r2 x284r3 x2a8r4 x2a8r5 x2a8r6 x2a8r7 x2a8r8 x2a8r9 x284r10 x2a8r11 x2a8r12 x284m128 x284m136 x2a8m144 x284m176 x284m240 x284m248 x284m256 ∧ x2a8r4 = (BitVec.ofNat 64 x284r1 * BitVec.ofNat 64 x284r1).toNat ∧ x2a8r5 = (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r1) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r1))).toNat ∧ x2a8r6 = (BitVec.ofNat 64 x284r2 * BitVec.ofNat 64 x284r1).toNat ∧ x2a8r7 = (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r2) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r1))).toNat ∧ x2a8r8 = (BitVec.ofNat 64 x284r0 * BitVec.ofNat 64 x284r1).toNat ∧ x2a8r9 = (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r0) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r1))).toNat ∧ x2a8r11 = (BitVec.ofNat 64 x284r2 * BitVec.ofNat 64 x284r2).toNat ∧ x2a8r12 = (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r2) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r2))).toNat ∧ x2a8m144 = x284r0 % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_284_2a8 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0x284)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (x284r0 x284r1 x284r2 x284r3 x284r10 x284m128 x284m136 x284m176 x284m240 x284m248 x284m256 : Nat) (hL : L284 S x284r0 x284r1 x284r2 x284r3 x284r10 x284m128 x284m136 x284m176 x284m240 x284m248 x284m256) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x2a8)) S (P_284_2a8 s x284r0 x284r1 x284r2 x284r3 x284r10 x284m128 x284m136 x284m176 x284m240 x284m248 x284m256) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 328 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 280 by omega]; exact hsd
  obtain ⟨hE_x284r0, hB_x284r0, hE_x284r1, hB_x284r1, hE_x284r2, hB_x284r2, hE_x284r3, hB_x284r3, hE_x284r10, hB_x284r10, hE_x284m128, hB_x284m128, hE_x284m136, hB_x284m136, hE_x284m176, hB_x284m176, hE_x284m240, hB_x284m240, hE_x284m248, hB_x284m248, hE_x284m256, hB_x284m256⟩ := hL
  janus_run [hE_x284r0, hE_x284r1, hE_x284r2, hE_x284r3, hE_x284r10, hE_x284m128, hE_x284m136, hE_x284m176, hE_x284m240, hE_x284m248, hE_x284m256, Nat.mod_eq_of_lt hB_x284r0, Nat.mod_eq_of_lt hB_x284r1, Nat.mod_eq_of_lt hB_x284r2, Nat.mod_eq_of_lt hB_x284r3, Nat.mod_eq_of_lt hB_x284r10, Nat.mod_eq_of_lt hB_x284m128, Nat.mod_eq_of_lt hB_x284m136, Nat.mod_eq_of_lt hB_x284m176, Nat.mod_eq_of_lt hB_x284m240, Nat.mod_eq_of_lt hB_x284m248, Nat.mod_eq_of_lt hB_x284m256, Fv256.B.rot32_and, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [recEntry + 0x2a8]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  unfold P_284_2a8
  refine ⟨(BitVec.ofNat 64 x284r1 * BitVec.ofNat 64 x284r1).toNat, (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r1) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r1))).toNat, (BitVec.ofNat 64 x284r2 * BitVec.ofNat 64 x284r1).toNat, (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r2) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r1))).toNat, (BitVec.ofNat 64 x284r0 * BitVec.ofNat 64 x284r1).toNat, (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r0) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r1))).toNat, (BitVec.ofNat 64 x284r2 * BitVec.ofNat 64 x284r2).toNat, (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 x284r2) * BitVec.setWidth 128 (BitVec.ofNat 64 x284r2))).toNat, x284r0 % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L2a8
    and_intros
    · first | exact hE_x284r0 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x284r0)
    · exact hB_x284r0
    · first | exact hE_x284r2 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x284r2)
    · exact hB_x284r2
    · first | exact hE_x284r3 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x284r3)
    · exact hB_x284r3
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x284r10 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x284r10)
    · exact hB_x284r10
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x284m128 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x284m128)
    · exact hB_x284m128
    · first | exact hE_x284m136 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x284m136)
    · exact hB_x284m136
    · first | with_reducible rfl | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x284m176 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x284m176)
    · exact hB_x284m176
    · first | exact hE_x284m240 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x284m240)
    · exact hB_x284m240
    · first | exact hE_x284m248 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x284m248)
    · exact hB_x284m248
    · first | exact hE_x284m256 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x284m256)
    · exact hB_x284m256
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
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
