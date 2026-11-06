import Fv256.Arm64.R4Live

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec

namespace Fv256.Arm64.R4Seg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

def P_2b4_2f4 (s : State) (x2b4r1 x2b4r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x2b4r12 x2b4m72 : Nat) (S' : State) : Prop :=
  ∃ x2f4r3 x2f4r4 x2f4r5 x2f4r6 x2f4r7, L2f4 S' x2b4r1 x2b4r2 x2f4r3 x2f4r4 x2f4r5 x2f4r6 x2f4r7 x2b4m72 0 x2b4r12 ∧ x2f4r3 = (if x2b4r8 = 0 then x2b4r3 else (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) % 18446744073709551616) ∧ x2f4r4 = (if x2b4r8 = 0 then x2b4r4 else (x2b4r4 + x2b4r12 + (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) ∧ x2f4r5 = (if x2b4r8 = 0 then x2b4r5 else (x2b4r5 + (x2b4r6 + x2b4m72 + (x2b4r4 + x2b4r12 + (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) ∧ x2f4r6 = (if x2b4r8 = 0 then x2b4r6 else (x2b4r6 + x2b4m72 + (x2b4r4 + x2b4r12 + (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616) ∧ x2f4r7 = (if x2b4r8 = 0 then x2b4r7 else (x2b4r7 + x2b4r2) % 18446744073709551616) ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_2b4_2f4 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (r4Entry + 0x2b4)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x2b4r1 x2b4r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x2b4r12 x2b4m72 : Nat) (hL : L2b4 S x2b4r1 x2b4r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x2b4r12 x2b4m72) :
    ReachesRet Fv256.Arm64.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x2f4)) S (P_2b4_2f4 s x2b4r1 x2b4r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x2b4r12 x2b4m72) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hbz, hbx, hbm, hbu, hm3, hmu⟩ := hs
  have hax1 : S.mem.accessible (s.regs 1).toNat 64 false = true := by rw [hM.2.2.accessible]; exact hbx.2.1
  have hax2 : S.mem.accessible (s.regs 2).toNat 32 false = true := by rw [hM.2.2.accessible]; exact hbm.2.1
  have hax3 : S.mem.accessible (s.regs 3).toNat 40 false = true := by rw [hM.2.2.accessible]; exact hbu.2.1
  have hbx1 := hbx.1
  have hbm1 := hbm.1
  have hbu1 := hbu.1
  have hin1_0 : S.mem.readLE ((s.regs 1).toNat) 8 = s.mem.readLE ((s.regs 1).toNat) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin1_1 : S.mem.readLE ((s.regs 1).toNat + 8) 8 = s.mem.readLE ((s.regs 1).toNat + 8) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin1_2 : S.mem.readLE ((s.regs 1).toNat + 16) 8 = s.mem.readLE ((s.regs 1).toNat + 16) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin1_3 : S.mem.readLE ((s.regs 1).toNat + 24) 8 = s.mem.readLE ((s.regs 1).toNat + 24) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin1_4 : S.mem.readLE ((s.regs 1).toNat + 32) 8 = s.mem.readLE ((s.regs 1).toNat + 32) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin1_5 : S.mem.readLE ((s.regs 1).toNat + 40) 8 = s.mem.readLE ((s.regs 1).toNat + 40) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin1_6 : S.mem.readLE ((s.regs 1).toNat + 48) 8 = s.mem.readLE ((s.regs 1).toNat + 48) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin1_7 : S.mem.readLE ((s.regs 1).toNat + 56) 8 = s.mem.readLE ((s.regs 1).toNat + 56) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin2_0 : S.mem.readLE ((s.regs 2).toNat) 8 = s.mem.readLE ((s.regs 2).toNat) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin2_1 : S.mem.readLE ((s.regs 2).toNat + 8) 8 = s.mem.readLE ((s.regs 2).toNat + 8) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin2_2 : S.mem.readLE ((s.regs 2).toNat + 16) 8 = s.mem.readLE ((s.regs 2).toNat + 16) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin2_3 : S.mem.readLE ((s.regs 2).toNat + 24) 8 = s.mem.readLE ((s.regs 2).toNat + 24) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin3_0 : S.mem.readLE ((s.regs 3).toNat) 8 = s.mem.readLE ((s.regs 3).toNat) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin3_1 : S.mem.readLE ((s.regs 3).toNat + 8) 8 = s.mem.readLE ((s.regs 3).toNat + 8) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin3_2 : S.mem.readLE ((s.regs 3).toNat + 16) 8 = s.mem.readLE ((s.regs 3).toNat + 16) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin3_3 : S.mem.readLE ((s.regs 3).toNat + 24) 8 = s.mem.readLE ((s.regs 3).toNat + 24) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hin3_4 : S.mem.readLE ((s.regs 3).toNat + 32) 8 = s.mem.readLE ((s.regs 3).toNat + 32) 8 := hM.2.2.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 184 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 168 by omega]; exact hsd
  obtain ⟨hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72⟩ := hL
  have hB_x2b4r1 : x2b4r1 < 2 ^ 64 := by rw [← hE_x2b4r1]; exact BitVec.isLt _
  have hR_x2b4r1 : S.regs 1 = BitVec.ofNat 64 x2b4r1 := by rw [← hE_x2b4r1]; exact bv_eq_ofNat _
  have hB_x2b4r2 : x2b4r2 < 2 ^ 64 := by rw [← hE_x2b4r2]; exact BitVec.isLt _
  have hR_x2b4r2 : S.regs 2 = BitVec.ofNat 64 x2b4r2 := by rw [← hE_x2b4r2]; exact bv_eq_ofNat _
  have hB_x2b4r3 : x2b4r3 < 2 ^ 64 := by rw [← hE_x2b4r3]; exact BitVec.isLt _
  have hR_x2b4r3 : S.regs 3 = BitVec.ofNat 64 x2b4r3 := by rw [← hE_x2b4r3]; exact bv_eq_ofNat _
  have hB_x2b4r4 : x2b4r4 < 2 ^ 64 := by rw [← hE_x2b4r4]; exact BitVec.isLt _
  have hR_x2b4r4 : S.regs 4 = BitVec.ofNat 64 x2b4r4 := by rw [← hE_x2b4r4]; exact bv_eq_ofNat _
  have hB_x2b4r5 : x2b4r5 < 2 ^ 64 := by rw [← hE_x2b4r5]; exact BitVec.isLt _
  have hR_x2b4r5 : S.regs 5 = BitVec.ofNat 64 x2b4r5 := by rw [← hE_x2b4r5]; exact bv_eq_ofNat _
  have hB_x2b4r6 : x2b4r6 < 2 ^ 64 := by rw [← hE_x2b4r6]; exact BitVec.isLt _
  have hR_x2b4r6 : S.regs 6 = BitVec.ofNat 64 x2b4r6 := by rw [← hE_x2b4r6]; exact bv_eq_ofNat _
  have hB_x2b4r7 : x2b4r7 < 2 ^ 64 := by rw [← hE_x2b4r7]; exact BitVec.isLt _
  have hR_x2b4r7 : S.regs 7 = BitVec.ofNat 64 x2b4r7 := by rw [← hE_x2b4r7]; exact bv_eq_ofNat _
  have hB_x2b4r8 : x2b4r8 < 2 ^ 64 := by rw [← hE_x2b4r8]; exact BitVec.isLt _
  have hR_x2b4r8 : S.regs 8 = BitVec.ofNat 64 x2b4r8 := by rw [← hE_x2b4r8]; exact bv_eq_ofNat _
  have hB_x2b4r12 : x2b4r12 < 2 ^ 64 := by rw [← hE_x2b4r12]; exact BitVec.isLt _
  have hR_x2b4r12 : S.regs 12 = BitVec.ofNat 64 x2b4r12 := by rw [← hE_x2b4r12]; exact bv_eq_ofNat _
  have hB_x2b4m72 : x2b4m72 < 2 ^ 64 := by rw [← hE_x2b4m72]; exact Util.readLE8_lt _ _
  janus_run [hR_x2b4r1, hR_x2b4r2, hR_x2b4r3, hR_x2b4r4, hR_x2b4r5, hR_x2b4r6, hR_x2b4r7, hR_x2b4r8, hR_x2b4r12, hE_x2b4m72, Nat.mod_eq_of_lt hB_x2b4r1, Nat.mod_eq_of_lt hB_x2b4r2, Nat.mod_eq_of_lt hB_x2b4r3, Nat.mod_eq_of_lt hB_x2b4r4, Nat.mod_eq_of_lt hB_x2b4r5, Nat.mod_eq_of_lt hB_x2b4r6, Nat.mod_eq_of_lt hB_x2b4r7, Nat.mod_eq_of_lt hB_x2b4r8, Nat.mod_eq_of_lt hB_x2b4r12, Nat.mod_eq_of_lt hB_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [r4Entry + 0x2f4]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [r4Entry, segAddr]) ?_
  unfold P_2b4_2f4
  refine ⟨(if x2b4r8 = 0 then x2b4r3 else (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) % 18446744073709551616), (if x2b4r8 = 0 then x2b4r4 else (x2b4r4 + x2b4r12 + (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616), (if x2b4r8 = 0 then x2b4r5 else (x2b4r5 + (x2b4r6 + x2b4m72 + (x2b4r4 + x2b4r12 + (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616), (if x2b4r8 = 0 then x2b4r6 else (x2b4r6 + x2b4m72 + (x2b4r4 + x2b4r12 + (x2b4r3 + x2b4r1 + (x2b4r7 + x2b4r2) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616), (if x2b4r8 = 0 then x2b4r7 else (x2b4r7 + x2b4r2) % 18446744073709551616), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L2f4
    and_intros
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4]
    · first
        | (rw [if_pos hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
        | (rw [if_neg hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
    · first
        | (rw [if_pos hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
        | (rw [if_neg hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
    · first
        | (rw [if_pos hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
        | (rw [if_neg hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
    · first
        | (rw [if_pos hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
        | (rw [if_neg hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
    · first
        | (rw [if_pos hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
        | (rw [if_neg hbr]; dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4])
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Bool.toNat_true, Bool.toNat_false, hE_x2b4r1, hE_x2b4r2, hE_x2b4r3, hE_x2b4r4, hE_x2b4r5, hE_x2b4r6, hE_x2b4r7, hE_x2b4r8, hE_x2b4r12, hE_x2b4m72, hin1_0, hin1_1, hin1_2, hin1_3, hin1_4, hin1_5, hin1_6, hin1_7, hin2_0, hin2_1, hin2_2, hin2_3, hin3_0, hin3_1, hin3_2, hin3_3, hin3_4]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · refine ⟨hR.1, ?_, ?_⟩
    · first | exact hR.2.1 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.1)
    · first | exact hR.2.2 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.2)
  · dsimp only
    repeat (refine R4Mem.write ?_ _ _ _ (by omega) (by omega) (by omega) hsb)
    exact hM
  )

end Fv256.Arm64.R4Seg
