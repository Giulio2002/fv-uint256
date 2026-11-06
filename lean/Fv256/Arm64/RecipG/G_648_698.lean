import Fv256.Arm64.RecipLive

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

def P_648_698 (s : State) (x648r0 x648r1 x648r2 x648r3 x648r4 x648r5 x648r6 x648r7 x648r8 x648r9 x648r10 x648r11 x648r12 x648m80 x648m88 x648m96 x648m104 x648m168 x648m176 x648m184 : Nat) (S' : State) : Prop :=
  ∃ x698r0, L698 S' x698r0 x648m104 x648r4 x648r10 x648m80 x648m88 x648m96 x648m176 ∧ x698r0 = (18446744073709551616 - (18446744073709551615 + (4611686018427387904 + (18446744073709551616 - 1 - (x648r12 + x648r10 + (x648r3 + x648r2 + (x648r1 + x648r11 + (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648r3 + x648r2 + (x648r1 + x648r11 + (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648r1 + x648r11 + (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648r5 + x648r6) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - x648r7) + (x648r10 + (18446744073709551616 - 1 - x648r9) + (x648r10 + (18446744073709551616 - 1 - x648r8) + (decide (x648m168 ≤ x648r10)).toNat) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_648_698 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0x648)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (x648r0 x648r1 x648r2 x648r3 x648r4 x648r5 x648r6 x648r7 x648r8 x648r9 x648r10 x648r11 x648r12 x648m80 x648m88 x648m96 x648m104 x648m168 x648m176 x648m184 : Nat) (hL : L648 S x648r0 x648r1 x648r2 x648r3 x648r4 x648r5 x648r6 x648r7 x648r8 x648r9 x648r10 x648r11 x648r12 x648m80 x648m88 x648m96 x648m104 x648m168 x648m176 x648m184) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x698)) S (P_648_698 s x648r0 x648r1 x648r2 x648r3 x648r4 x648r5 x648r6 x648r7 x648r8 x648r9 x648r10 x648r11 x648r12 x648m80 x648m88 x648m96 x648m104 x648m168 x648m176 x648m184) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 328 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 280 by omega]; exact hsd
  obtain ⟨hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184⟩ := hL
  have hB_x648r0 : x648r0 < 2 ^ 64 := by rw [← hE_x648r0]; exact BitVec.isLt _
  have hR_x648r0 : S.regs 0 = BitVec.ofNat 64 x648r0 := by rw [← hE_x648r0]; exact bv_eq_ofNat _
  have hB_x648r1 : x648r1 < 2 ^ 64 := by rw [← hE_x648r1]; exact BitVec.isLt _
  have hR_x648r1 : S.regs 1 = BitVec.ofNat 64 x648r1 := by rw [← hE_x648r1]; exact bv_eq_ofNat _
  have hB_x648r2 : x648r2 < 2 ^ 64 := by rw [← hE_x648r2]; exact BitVec.isLt _
  have hR_x648r2 : S.regs 2 = BitVec.ofNat 64 x648r2 := by rw [← hE_x648r2]; exact bv_eq_ofNat _
  have hB_x648r3 : x648r3 < 2 ^ 64 := by rw [← hE_x648r3]; exact BitVec.isLt _
  have hR_x648r3 : S.regs 3 = BitVec.ofNat 64 x648r3 := by rw [← hE_x648r3]; exact bv_eq_ofNat _
  have hB_x648r4 : x648r4 < 2 ^ 64 := by rw [← hE_x648r4]; exact BitVec.isLt _
  have hR_x648r4 : S.regs 4 = BitVec.ofNat 64 x648r4 := by rw [← hE_x648r4]; exact bv_eq_ofNat _
  have hB_x648r5 : x648r5 < 2 ^ 64 := by rw [← hE_x648r5]; exact BitVec.isLt _
  have hR_x648r5 : S.regs 5 = BitVec.ofNat 64 x648r5 := by rw [← hE_x648r5]; exact bv_eq_ofNat _
  have hB_x648r6 : x648r6 < 2 ^ 64 := by rw [← hE_x648r6]; exact BitVec.isLt _
  have hR_x648r6 : S.regs 6 = BitVec.ofNat 64 x648r6 := by rw [← hE_x648r6]; exact bv_eq_ofNat _
  have hB_x648r7 : x648r7 < 2 ^ 64 := by rw [← hE_x648r7]; exact BitVec.isLt _
  have hR_x648r7 : S.regs 7 = BitVec.ofNat 64 x648r7 := by rw [← hE_x648r7]; exact bv_eq_ofNat _
  have hB_x648r8 : x648r8 < 2 ^ 64 := by rw [← hE_x648r8]; exact BitVec.isLt _
  have hR_x648r8 : S.regs 8 = BitVec.ofNat 64 x648r8 := by rw [← hE_x648r8]; exact bv_eq_ofNat _
  have hB_x648r9 : x648r9 < 2 ^ 64 := by rw [← hE_x648r9]; exact BitVec.isLt _
  have hR_x648r9 : S.regs 9 = BitVec.ofNat 64 x648r9 := by rw [← hE_x648r9]; exact bv_eq_ofNat _
  have hB_x648r10 : x648r10 < 2 ^ 64 := by rw [← hE_x648r10]; exact BitVec.isLt _
  have hR_x648r10 : S.regs 10 = BitVec.ofNat 64 x648r10 := by rw [← hE_x648r10]; exact bv_eq_ofNat _
  have hB_x648r11 : x648r11 < 2 ^ 64 := by rw [← hE_x648r11]; exact BitVec.isLt _
  have hR_x648r11 : S.regs 11 = BitVec.ofNat 64 x648r11 := by rw [← hE_x648r11]; exact bv_eq_ofNat _
  have hB_x648r12 : x648r12 < 2 ^ 64 := by rw [← hE_x648r12]; exact BitVec.isLt _
  have hR_x648r12 : S.regs 12 = BitVec.ofNat 64 x648r12 := by rw [← hE_x648r12]; exact bv_eq_ofNat _
  have hB_x648m80 : x648m80 < 2 ^ 64 := by rw [← hE_x648m80]; exact Util.readLE8_lt _ _
  have hB_x648m88 : x648m88 < 2 ^ 64 := by rw [← hE_x648m88]; exact Util.readLE8_lt _ _
  have hB_x648m96 : x648m96 < 2 ^ 64 := by rw [← hE_x648m96]; exact Util.readLE8_lt _ _
  have hB_x648m104 : x648m104 < 2 ^ 64 := by rw [← hE_x648m104]; exact Util.readLE8_lt _ _
  have hB_x648m168 : x648m168 < 2 ^ 64 := by rw [← hE_x648m168]; exact Util.readLE8_lt _ _
  have hB_x648m176 : x648m176 < 2 ^ 64 := by rw [← hE_x648m176]; exact Util.readLE8_lt _ _
  have hB_x648m184 : x648m184 < 2 ^ 64 := by rw [← hE_x648m184]; exact Util.readLE8_lt _ _
  janus_run [hR_x648r0, hR_x648r1, hR_x648r2, hR_x648r3, hR_x648r4, hR_x648r5, hR_x648r6, hR_x648r7, hR_x648r8, hR_x648r9, hR_x648r10, hR_x648r11, hR_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184, Nat.mod_eq_of_lt hB_x648r0, Nat.mod_eq_of_lt hB_x648r1, Nat.mod_eq_of_lt hB_x648r2, Nat.mod_eq_of_lt hB_x648r3, Nat.mod_eq_of_lt hB_x648r4, Nat.mod_eq_of_lt hB_x648r5, Nat.mod_eq_of_lt hB_x648r6, Nat.mod_eq_of_lt hB_x648r7, Nat.mod_eq_of_lt hB_x648r8, Nat.mod_eq_of_lt hB_x648r9, Nat.mod_eq_of_lt hB_x648r10, Nat.mod_eq_of_lt hB_x648r11, Nat.mod_eq_of_lt hB_x648r12, Nat.mod_eq_of_lt hB_x648m80, Nat.mod_eq_of_lt hB_x648m88, Nat.mod_eq_of_lt hB_x648m96, Nat.mod_eq_of_lt hB_x648m104, Nat.mod_eq_of_lt hB_x648m168, Nat.mod_eq_of_lt hB_x648m176, Nat.mod_eq_of_lt hB_x648m184, Fv256.B.rot32_and, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [recEntry + 0x698]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  unfold P_648_698
  refine ⟨(18446744073709551616 - (18446744073709551615 + (4611686018427387904 + (18446744073709551616 - 1 - (x648r12 + x648r10 + (x648r3 + x648r2 + (x648r1 + x648r11 + (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648r3 + x648r2 + (x648r1 + x648r11 + (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648r1 + x648r11 + (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648m184 + x648r0 + (x648r5 + x648r6) / 18446744073709551616) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - (x648r5 + x648r6) % 18446744073709551616) + (x648r10 + (18446744073709551616 - 1 - x648r7) + (x648r10 + (18446744073709551616 - 1 - x648r9) + (x648r10 + (18446744073709551616 - 1 - x648r8) + (decide (x648m168 ≤ x648r10)).toNat) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_⟩
  · unfold L698
    and_intros
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x648r0, hE_x648r1, hE_x648r2, hE_x648r3, hE_x648r4, hE_x648r5, hE_x648r6, hE_x648r7, hE_x648r8, hE_x648r9, hE_x648r10, hE_x648r11, hE_x648r12, hE_x648m80, hE_x648m88, hE_x648m96, hE_x648m104, hE_x648m168, hE_x648m176, hE_x648m184]
  · rfl
  · refine ⟨hR.1, ?_, ?_⟩
    · first | exact hR.2.1 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.1)
    · first | exact hR.2.2 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.2)
  · dsimp only
    repeat (refine RecMem.write ?_ _ _ _ (by omega) (by omega) hsb)
    exact hM
  )

end Fv256.Arm64.RecipSeg
