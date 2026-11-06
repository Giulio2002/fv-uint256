import Fv256.Arm64.RecipLive

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

def P_708_77c (s : State) (x708r0 x708r1 x708r2 x708r3 x708r4 x708r5 : Nat) (S' : State) : Prop :=
  ∃ x77cm280 x77cm288 x77cm296 x77cm304 x77cm312, L77c S' x77cm280 x77cm288 x77cm296 x77cm304 x77cm312 ∧ x77cm280 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then (if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r1 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64) ||| BitVec.ofNat 64 x708r0 >>> (x708r5 % 64) else BitVec.ofNat 64 x708r0).toNat ∧ x77cm288 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then (if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r2 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64) ||| BitVec.ofNat 64 x708r1 >>> (x708r5 % 64) else BitVec.ofNat 64 x708r1).toNat ∧ x77cm296 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then BitVec.ofNat 64 x708r2 >>> (x708r5 % 64) ||| if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r3 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64 else BitVec.ofNat 64 x708r2).toNat ∧ x77cm304 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then BitVec.ofNat 64 x708r3 >>> (x708r5 % 64) ||| if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r4 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64 else BitVec.ofNat 64 x708r3).toNat ∧ x77cm312 = (if 0 < (BitVec.ofNat 64 x708r5).toInt then BitVec.ofNat 64 x708r4 >>> (x708r5 % 64) else BitVec.ofNat 64 x708r4).toNat ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_708_77c (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0x708)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (x708r0 x708r1 x708r2 x708r3 x708r4 x708r5 : Nat) (hL : L708 S x708r0 x708r1 x708r2 x708r3 x708r4 x708r5) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x77c)) S (P_708_77c s x708r0 x708r1 x708r2 x708r3 x708r4 x708r5) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 328 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 280 by omega]; exact hsd
  obtain ⟨hE_x708r0, hE_x708r1, hE_x708r2, hE_x708r3, hE_x708r4, hE_x708r5⟩ := hL
  have hB_x708r0 : x708r0 < 2 ^ 64 := by rw [← hE_x708r0]; exact BitVec.isLt _
  have hR_x708r0 : S.regs 0 = BitVec.ofNat 64 x708r0 := by rw [← hE_x708r0]; exact bv_eq_ofNat _
  have hB_x708r1 : x708r1 < 2 ^ 64 := by rw [← hE_x708r1]; exact BitVec.isLt _
  have hR_x708r1 : S.regs 1 = BitVec.ofNat 64 x708r1 := by rw [← hE_x708r1]; exact bv_eq_ofNat _
  have hB_x708r2 : x708r2 < 2 ^ 64 := by rw [← hE_x708r2]; exact BitVec.isLt _
  have hR_x708r2 : S.regs 2 = BitVec.ofNat 64 x708r2 := by rw [← hE_x708r2]; exact bv_eq_ofNat _
  have hB_x708r3 : x708r3 < 2 ^ 64 := by rw [← hE_x708r3]; exact BitVec.isLt _
  have hR_x708r3 : S.regs 3 = BitVec.ofNat 64 x708r3 := by rw [← hE_x708r3]; exact bv_eq_ofNat _
  have hB_x708r4 : x708r4 < 2 ^ 64 := by rw [← hE_x708r4]; exact BitVec.isLt _
  have hR_x708r4 : S.regs 4 = BitVec.ofNat 64 x708r4 := by rw [← hE_x708r4]; exact bv_eq_ofNat _
  have hB_x708r5 : x708r5 < 2 ^ 64 := by rw [← hE_x708r5]; exact BitVec.isLt _
  have hR_x708r5 : S.regs 5 = BitVec.ofNat 64 x708r5 := by rw [← hE_x708r5]; exact bv_eq_ofNat _
  janus_run [hR_x708r0, hR_x708r1, hR_x708r2, hR_x708r3, hR_x708r4, hR_x708r5, Nat.mod_eq_of_lt hB_x708r0, Nat.mod_eq_of_lt hB_x708r1, Nat.mod_eq_of_lt hB_x708r2, Nat.mod_eq_of_lt hB_x708r3, Nat.mod_eq_of_lt hB_x708r4, Nat.mod_eq_of_lt hB_x708r5, Fv256.B.rot32_and, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [recEntry + 0x77c]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  unfold P_708_77c
  refine ⟨(if 0 < (BitVec.ofNat 64 x708r5).toInt then (if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r1 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64) ||| BitVec.ofNat 64 x708r0 >>> (x708r5 % 64) else BitVec.ofNat 64 x708r0).toNat, (if 0 < (BitVec.ofNat 64 x708r5).toInt then (if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r2 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64) ||| BitVec.ofNat 64 x708r1 >>> (x708r5 % 64) else BitVec.ofNat 64 x708r1).toNat, (if 0 < (BitVec.ofNat 64 x708r5).toInt then BitVec.ofNat 64 x708r2 >>> (x708r5 % 64) ||| if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r3 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64 else BitVec.ofNat 64 x708r2).toNat, (if 0 < (BitVec.ofNat 64 x708r5).toInt then BitVec.ofNat 64 x708r3 >>> (x708r5 % 64) ||| if (18446744073709551616 - x708r5 + 64) % 18446744073709551616 < 64 then BitVec.ofNat 64 (x708r4 * 2 ^ ((18446744073709551616 - x708r5 - 18446744073709551552) % 64)) else 0#64 else BitVec.ofNat 64 x708r3).toNat, (if 0 < (BitVec.ofNat 64 x708r5).toInt then BitVec.ofNat 64 x708r4 >>> (x708r5 % 64) else BitVec.ofNat 64 x708r4).toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L77c
    and_intros
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x708r0, hE_x708r1, hE_x708r2, hE_x708r3, hE_x708r4, hE_x708r5]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x708r0, hE_x708r1, hE_x708r2, hE_x708r3, hE_x708r4, hE_x708r5]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x708r0, hE_x708r1, hE_x708r2, hE_x708r3, hE_x708r4, hE_x708r5]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x708r0, hE_x708r1, hE_x708r2, hE_x708r3, hE_x708r4, hE_x708r5]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_x708r0, hE_x708r1, hE_x708r2, hE_x708r3, hE_x708r4, hE_x708r5]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · refine ⟨hR.1, ?_, ?_⟩
    · first | exact hR.2.1 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.1)
    · first | exact hR.2.2 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.2)
  · dsimp only
    repeat (refine RecMem.write ?_ _ _ _ (by omega) (by omega) (by omega) hsb)
    exact hM
  )

end Fv256.Arm64.RecipSeg
