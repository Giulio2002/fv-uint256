import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_7ae_801 (s : State) (y3 : Nat) (x7aerax x7aercx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x7aem98 x7aema0 x7aema8 x7aem208 x7aem210 x7aem218 x7aem220 : Nat) (S' : State) : Prop :=
  ∃ x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60, L801 s S' x7aercx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x7aem208 x7aem210 x7aem218 x7aem220 ∧ x801rdx = (0 % 18446744073709551616 + 18446744073709551616 - x7aerbx % 18446744073709551616 - (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat) % 18446744073709551616 ∧ x801rbx = (0 % 18446744073709551616 + 18446744073709551616 - x7aer8 % 18446744073709551616 - (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat) % 18446744073709551616 ∧ x801rsi = (x7aema8 % 18446744073709551616 + 18446744073709551616 - x7aerdi % 18446744073709551616 - (1 - (x7aem98 + (18446744073709551616 - x7aersi - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616 ∧ x801r8 = (x7aema0 % 18446744073709551616 + 18446744073709551616 - x7aerax % 18446744073709551616 - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616 ∧ x801r9 = (x7aem98 % 18446744073709551616 + 18446744073709551616 - x7aersi % 18446744073709551616 - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616)) % 18446744073709551616 ∧ x801m40 = (x7aema8 % 18446744073709551616 + 18446744073709551616 - x7aerdi % 18446744073709551616 - (1 - (x7aem98 + (18446744073709551616 - x7aersi - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616 ∧ x801m48 = (x7aem98 % 18446744073709551616 + 18446744073709551616 - x7aersi % 18446744073709551616 - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616)) % 18446744073709551616 ∧ x801m50 = (x7aema0 % 18446744073709551616 + 18446744073709551616 - x7aerax % 18446744073709551616 - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616 ∧ x801m60 = (0 % 18446744073709551616 + 18446744073709551616 - x7aerbx % 18446744073709551616 - (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_7ae_801 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x7ae)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x7aerax x7aercx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x7aem98 x7aema0 x7aema8 x7aem208 x7aem210 x7aem218 x7aem220 : Nat) (hL : L7ae s S x7aerax x7aercx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x7aem98 x7aema0 x7aema8 x7aem208 x7aem210 x7aem218 x7aem220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x801)) S (P_7ae_801 s y3 x7aerax x7aercx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x7aem98 x7aema0 x7aema8 x7aem208 x7aem210 x7aem218 x7aem220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x7aerax, hB_x7aerax, hE_x7aercx, hB_x7aercx, hE_x7aerdx, hB_x7aerdx, hE_x7aerbx, hB_x7aerbx, hE_x7aersi, hB_x7aersi, hE_x7aerdi, hB_x7aerdi, hE_x7aer8, hB_x7aer8, hE_x7aer11, hB_x7aer11, hE_x7aem98, hB_x7aem98, hE_x7aema0, hB_x7aema0, hE_x7aema8, hB_x7aema8, hE_x7aem208, hB_x7aem208, hE_x7aem210, hB_x7aem210, hE_x7aem218, hB_x7aem218, hE_x7aem220, hB_x7aem220⟩ := hL
  janus64_run [Util.readLE_32, hE_x7aerax, hE_x7aercx, hE_x7aerdx, hE_x7aerbx, hE_x7aersi, hE_x7aerdi, hE_x7aer8, hE_x7aer11, hE_x7aem98, hE_x7aema0, hE_x7aema8, hE_x7aem208, hE_x7aem210, hE_x7aem218, hE_x7aem220, hsp4, Nat.mod_eq_of_lt hB_x7aerax, Nat.mod_eq_of_lt hB_x7aercx, Nat.mod_eq_of_lt hB_x7aerdx, Nat.mod_eq_of_lt hB_x7aerbx, Nat.mod_eq_of_lt hB_x7aersi, Nat.mod_eq_of_lt hB_x7aerdi, Nat.mod_eq_of_lt hB_x7aer8, Nat.mod_eq_of_lt hB_x7aer11, Nat.mod_eq_of_lt hB_x7aem98, Nat.mod_eq_of_lt hB_x7aema0, Nat.mod_eq_of_lt hB_x7aema8, Nat.mod_eq_of_lt hB_x7aem208, Nat.mod_eq_of_lt hB_x7aem210, Nat.mod_eq_of_lt hB_x7aem218, Nat.mod_eq_of_lt hB_x7aem220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_7ae_801
  refine ⟨(0 % 18446744073709551616 + 18446744073709551616 - x7aerbx % 18446744073709551616 - (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat) % 18446744073709551616, (0 % 18446744073709551616 + 18446744073709551616 - x7aer8 % 18446744073709551616 - (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat) % 18446744073709551616, (x7aema8 % 18446744073709551616 + 18446744073709551616 - x7aerdi % 18446744073709551616 - (1 - (x7aem98 + (18446744073709551616 - x7aersi - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616, (x7aema0 % 18446744073709551616 + 18446744073709551616 - x7aerax % 18446744073709551616 - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616, (x7aem98 % 18446744073709551616 + 18446744073709551616 - x7aersi % 18446744073709551616 - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616)) % 18446744073709551616, (x7aema8 % 18446744073709551616 + 18446744073709551616 - x7aerdi % 18446744073709551616 - (1 - (x7aem98 + (18446744073709551616 - x7aersi - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616, (x7aem98 % 18446744073709551616 + 18446744073709551616 - x7aersi % 18446744073709551616 - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616)) % 18446744073709551616, (x7aema0 % 18446744073709551616 + 18446744073709551616 - x7aerax % 18446744073709551616 - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616, (0 % 18446744073709551616 + 18446744073709551616 - x7aerbx % 18446744073709551616 - (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L801
    and_intros
    · first | exact hE_x7aercx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x7aercx)
    · exact hB_x7aercx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x7aem208
    · exact hB_x7aem208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x7aem210
    · exact hB_x7aem210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x7aem218
    · exact hB_x7aem218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x7aem220
    · exact hB_x7aem220
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold RecRegs
    and_intros
    · simp [setRegF, hr4]
    · simp [setRegF, hr5]
    · simp [setRegF, hr14]
    · simp [hx]
  · repeat (refine RecMem.write ?_ _ _ _ hlow ?_ ?_ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.RecipSeg
