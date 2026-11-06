import Fv256.Arm64.RecipLive

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

def P_bc_108 (s : State) (xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176 : Nat) (S' : State) : Prop :=
  ∃ x108r0 x108m176, L108 S' x108r0 18446744073709551615 xbcm48 xbcr3 xbcm32 xbcm40 x108m176 xbcm32 xbcm40 xbcm48 ∧ x108r0 = (if (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320) + (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320))) % 18446744073709551616 ||| xbcr3 * 2 % 18446744073709551616 = 0 then 18446744073709551615#64 else ((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)) + (((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)))).toNat ∧ x108m176 = (18446744073709551615 + xbcm176 % 64) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_bc_108 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0xbc)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176 : Nat) (hL : Lbc S xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176) (hX0 : xbcr0 % 2 ^ 32 = r0f xbcr3) (hX1 : 2 ^ 63 ≤ xbcr3) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x108)) S (P_bc_108 s xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 328 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 280 by omega]; exact hsd
  obtain ⟨hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176⟩ := hL
  have hB_xbcr0 : xbcr0 < 2 ^ 64 := by rw [← hE_xbcr0]; exact BitVec.isLt _
  have hR_xbcr0 : S.regs 0 = BitVec.ofNat 64 xbcr0 := by rw [← hE_xbcr0]; exact bv_eq_ofNat _
  have hB_xbcr3 : xbcr3 < 2 ^ 64 := by rw [← hE_xbcr3]; exact BitVec.isLt _
  have hR_xbcr3 : S.regs 3 = BitVec.ofNat 64 xbcr3 := by rw [← hE_xbcr3]; exact bv_eq_ofNat _
  have hB_xbcm32 : xbcm32 < 2 ^ 64 := by rw [← hE_xbcm32]; exact Util.readLE8_lt _ _
  have hB_xbcm40 : xbcm40 < 2 ^ 64 := by rw [← hE_xbcm40]; exact Util.readLE8_lt _ _
  have hB_xbcm48 : xbcm48 < 2 ^ 64 := by rw [← hE_xbcm48]; exact Util.readLE8_lt _ _
  have hB_xbcm176 : xbcm176 < 2 ^ 64 := by rw [← hE_xbcm176]; exact Util.readLE8_lt _ _
  janus_run [hR_xbcr0, hR_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176, Nat.mod_eq_of_lt hB_xbcr0, Nat.mod_eq_of_lt hB_xbcr3, Nat.mod_eq_of_lt hB_xbcm32, Nat.mod_eq_of_lt hB_xbcm40, Nat.mod_eq_of_lt hB_xbcm48, Nat.mod_eq_of_lt hB_xbcm176, Fv256.B.rot32_and, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [recEntry + 0x108]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  unfold P_bc_108
  refine ⟨(if (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320) + (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320))) % 18446744073709551616 ||| xbcr3 * 2 % 18446744073709551616 = 0 then 18446744073709551615#64 else ((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)) + (((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)))).toNat, (18446744073709551615 + xbcm176 % 64) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L108
    and_intros
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
    · dsimp only; simp (disch := omega) only [janus_post, setReg, ↓reduceIte, Nat.reduceEqDiff, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, Fv256.B.rot32_and, Bool.toNat_true, Bool.toNat_false, hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176]
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
