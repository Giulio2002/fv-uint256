import Fv256.Arm64.RecipLive

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg

def P_bc_108 (s : State) (xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176 : Nat) (S' : State) : Prop :=
  ∃ x108r0 x108r1 x108r2 x108r4 x108r5 x108m176 x108m240 x108m248 x108m256, L108 S' x108r0 x108r1 x108r2 xbcr3 x108r4 x108r5 x108m176 x108m240 x108m248 x108m256 ∧ x108r0 = (if (18446744073709551616 - (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))).toNat * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320) + (18446744073709551616 - (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))).toNat * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320))) % 18446744073709551616 ||| xbcr3 * 2 % 18446744073709551616 = 0 then 18446744073709551615#64 else ((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)) + (((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)))).toNat ∧ x108r1 = (18446744073709551615#64).toNat ∧ x108r2 = xbcm48 % 18446744073709551616 ∧ x108r4 = xbcm32 % 18446744073709551616 ∧ x108r5 = xbcm40 % 18446744073709551616 ∧ x108m176 = (18446744073709551615 + xbcm176 % 64) % 18446744073709551616 ∧ x108m240 = xbcm32 % 18446744073709551616 ∧ x108m248 = xbcm40 % 18446744073709551616 ∧ x108m256 = xbcm48 % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_bc_108 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0xbc)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176 : Nat) (hL : Lbc S xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176) (hX0 : xbcr0 % 2 ^ 32 = r0f xbcr3) (hX1 : 2 ^ 63 ≤ xbcr3) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x108)) S (P_bc_108 s xbcr0 xbcr3 xbcm32 xbcm40 xbcm48 xbcm176) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 328 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 280 by omega]; exact hsd
  obtain ⟨hE_xbcr0, hB_xbcr0, hE_xbcr3, hB_xbcr3, hE_xbcm32, hB_xbcm32, hE_xbcm40, hB_xbcm40, hE_xbcm48, hB_xbcm48, hE_xbcm176, hB_xbcm176⟩ := hL
  janus_run [hE_xbcr0, hE_xbcr3, hE_xbcm32, hE_xbcm40, hE_xbcm48, hE_xbcm176, Nat.mod_eq_of_lt hB_xbcr0, Nat.mod_eq_of_lt hB_xbcr3, Nat.mod_eq_of_lt hB_xbcm32, Nat.mod_eq_of_lt hB_xbcm40, Nat.mod_eq_of_lt hB_xbcm48, Nat.mod_eq_of_lt hB_xbcm176, Fv256.B.rot32_and, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [recEntry + 0x108]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  unfold P_bc_108
  refine ⟨(if (18446744073709551616 - (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))).toNat * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320) + (18446744073709551616 - (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))).toNat * xbcr3 / 18446744073709551616 + (((BitVec.ofNat 64 xbcr0).rotateRight 32).toNat &&& 18446744069414584320))) % 18446744073709551616 ||| xbcr3 * 2 % 18446744073709551616 = 0 then 18446744073709551615#64 else ((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)) + (((BitVec.ofNat 64 xbcr0).rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64) - BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0)) * BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 xbcr0))) * BitVec.setWidth 128 (BitVec.ofNat 64 xbcr3)))).toNat, (18446744073709551615#64).toNat, xbcm48 % 18446744073709551616, xbcm32 % 18446744073709551616, xbcm40 % 18446744073709551616, (18446744073709551615 + xbcm176 % 64) % 18446744073709551616, xbcm32 % 18446744073709551616, xbcm40 % 18446744073709551616, xbcm48 % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L108
    and_intros
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_xbcr3 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xbcr3)
    · exact hB_xbcr3
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
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
