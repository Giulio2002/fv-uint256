import Fv256.Arm64.RecipLive

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def P_88_bc (s : State) (x88m32 x88m40 x88m48 x88m56 x88m176 : Nat) (S' : State) : Prop :=
  ∃ xbcr0 xbcr3, Lbc S' xbcr0 xbcr3 x88m32 x88m40 x88m48 x88m176 ∧ xbcr0 = (if x88m56 / 2 ^ 32 % 2 ^ 32 = 2 ^ 31 then 2 ^ 64 - 1 else 2 ^ 63 / (x88m56 / 2 ^ 32)) ∧ xbcr3 = x88m56 % 18446744073709551616 ∧ xbcr0 % 2 ^ 32 = r0f xbcr3 ∧ 2 ^ 63 ≤ xbcr3 ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_88_bc (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0x88)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (x88m32 x88m40 x88m48 x88m56 x88m176 : Nat) (hL : L88 S x88m32 x88m40 x88m48 x88m56 x88m176) (hX0 : 2 ^ 63 ≤ x88m56) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xbc)) S (P_88_bc s x88m32 x88m40 x88m48 x88m56 x88m176) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 328 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 280 by omega]; exact hsd
  obtain ⟨hE_x88m32, hB_x88m32, hE_x88m40, hB_x88m40, hE_x88m48, hB_x88m48, hE_x88m56, hB_x88m56, hE_x88m176, hB_x88m176⟩ := hL
  janus_run [hE_x88m32, hE_x88m40, hE_x88m48, hE_x88m56, hE_x88m176, Nat.mod_eq_of_lt hB_x88m32, Nat.mod_eq_of_lt hB_x88m40, Nat.mod_eq_of_lt hB_x88m48, Nat.mod_eq_of_lt hB_x88m56, Nat.mod_eq_of_lt hB_x88m176, Fv256.B.rot32_and, BitVec.toNat_setWidth, BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.le_def, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add] until [recEntry + 0xbc]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  unfold P_88_bc
  refine ⟨(if x88m56 / 2 ^ 32 % 2 ^ 32 = 2 ^ 31 then 2 ^ 64 - 1 else 2 ^ 63 / (x88m56 / 2 ^ 32)), x88m56 % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Lbc
    and_intros
    · simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]
      by_cases hc : x88m56 / 2 ^ 32 % 2 ^ 32 = 2 ^ 31
      · first | (exfalso; omega) | (rw [if_pos hc]; try (first | rfl | decide | simp))
      · first | (exfalso; omega) | (rw [if_neg hc]; try (first | rfl | simp))
    · split <;> first | decide | exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
    · first | exact bv_eq_ofNat _ | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact bv_eq_ofNat _) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp [setReg]; done) | (simp [setReg, BitVec.ofNat_toNat]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x88m32 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x88m32)
    · exact hB_x88m32
    · first | exact hE_x88m40 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x88m40)
    · exact hB_x88m40
    · first | exact hE_x88m48 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x88m48)
    · exact hB_x88m48
    · first | exact hE_x88m176 | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x88m176)
    · exact hB_x88m176
  · with_reducible rfl
  · with_reducible rfl
  · have hB' : x88m56 < 18446744073709551616 := hB_x88m56
    unfold r0f
    by_cases hc : x88m56 / 2 ^ 32 % 2 ^ 32 = 2 ^ 31
    · first | (exfalso; omega) | (have hc2 : x88m56 / 2 ^ 32 = 2 ^ 31 := (by omega)
                                  rw [Nat.mod_eq_of_lt hB', if_pos hc, if_pos hc2]; try omega)
    · first | (exfalso; omega) | (have hc2 : ¬ (x88m56 / 2 ^ 32 = 2 ^ 31) := (by omega)
                                  rw [Nat.mod_eq_of_lt hB', if_neg hc, if_neg hc2]
                                  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega)))
  · omega
  · refine ⟨hR.1, ?_, ?_⟩
    · first | exact hR.2.1 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.1)
    · first | exact hR.2.2 | (simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]; exact hR.2.2)
  · dsimp only
    repeat (refine RecMem.write ?_ _ _ _ (by omega) (by omega) (by omega) hsb)
    exact hM
  )

end Fv256.Arm64.RecipSeg
