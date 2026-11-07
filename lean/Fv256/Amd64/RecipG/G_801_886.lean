import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_801_886 (s : State) (y3 : Nat) (x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 x801m220 : Nat) (S' : State) : Prop :=
  ∃ x886rax x886rdi x886r10 x886r11 x886r12 x886r13 x886r15 x886m68 x886m70 x886md8 x886me0 x886m100 x886m1f8 x886m200 x886m208, L886 s S' x886rax x801rcx x801rbx x801rsi x886rdi x801r8 x801r9 x886r10 x886r11 x886r12 x886r13 x886r15 x801m40 x801m48 x801m50 x801m60 x886m68 x886m70 x886md8 x886me0 x886m100 x886m1f8 x886m200 x886m208 x801m218 x801m220 ∧ x886rax = x801r8 % 18446744073709551616 ∧ x886rdi = x801rdx % 18446744073709551616 ∧ x886r10 = (x801m208 * x801rbx / 18446744073709551616) % 18446744073709551616 ∧ x886r11 = x801m210 % 18446744073709551616 ∧ x886r12 = (x801m208 * x801rdx / 18446744073709551616) % 18446744073709551616 ∧ x886r13 = (x801m208 * x801r8) % 18446744073709551616 ∧ x886r15 = (x801m208 * x801r8 / 18446744073709551616) % 18446744073709551616 ∧ x886m68 = (x801m208 * x801r9 / 18446744073709551616) % 18446744073709551616 ∧ x886m70 = (x801m208 * x801rbx) % 18446744073709551616 ∧ x886md8 = (x801m208 * x801rsi / 18446744073709551616) % 18446744073709551616 ∧ x886me0 = (x801m208 * x801rsi) % 18446744073709551616 ∧ x886m100 = (x801m208 * x801rdx) % 18446744073709551616 ∧ x886m1f8 = (x801m210 * x801rdx) % 18446744073709551616 ∧ x886m200 = (x801m210 * x801rdx / 18446744073709551616) % 18446744073709551616 ∧ x886m208 = (x801m208 * x801r9) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_801_886 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x801)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 x801m220 : Nat) (hL : L801 s S x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 x801m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x886)) S (P_801_886 s y3 x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 x801m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x801rcx, hB_x801rcx, hE_x801rdx, hB_x801rdx, hE_x801rbx, hB_x801rbx, hE_x801rsi, hB_x801rsi, hE_x801r8, hB_x801r8, hE_x801r9, hB_x801r9, hE_x801m40, hB_x801m40, hE_x801m48, hB_x801m48, hE_x801m50, hB_x801m50, hE_x801m60, hB_x801m60, hE_x801m208, hB_x801m208, hE_x801m210, hB_x801m210, hE_x801m218, hB_x801m218, hE_x801m220, hB_x801m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x801rcx, hE_x801rdx, hE_x801rbx, hE_x801rsi, hE_x801r8, hE_x801r9, hE_x801m40, hE_x801m48, hE_x801m50, hE_x801m60, hE_x801m208, hE_x801m210, hE_x801m218, hE_x801m220, hsp4, Nat.mod_eq_of_lt hB_x801rcx, Nat.mod_eq_of_lt hB_x801rdx, Nat.mod_eq_of_lt hB_x801rbx, Nat.mod_eq_of_lt hB_x801rsi, Nat.mod_eq_of_lt hB_x801r8, Nat.mod_eq_of_lt hB_x801r9, Nat.mod_eq_of_lt hB_x801m40, Nat.mod_eq_of_lt hB_x801m48, Nat.mod_eq_of_lt hB_x801m50, Nat.mod_eq_of_lt hB_x801m60, Nat.mod_eq_of_lt hB_x801m208, Nat.mod_eq_of_lt hB_x801m210, Nat.mod_eq_of_lt hB_x801m218, Nat.mod_eq_of_lt hB_x801m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_801_886
  refine ⟨x801r8 % 18446744073709551616, x801rdx % 18446744073709551616, (x801m208 * x801rbx / 18446744073709551616) % 18446744073709551616, x801m210 % 18446744073709551616, (x801m208 * x801rdx / 18446744073709551616) % 18446744073709551616, (x801m208 * x801r8) % 18446744073709551616, (x801m208 * x801r8 / 18446744073709551616) % 18446744073709551616, (x801m208 * x801r9 / 18446744073709551616) % 18446744073709551616, (x801m208 * x801rbx) % 18446744073709551616, (x801m208 * x801rsi / 18446744073709551616) % 18446744073709551616, (x801m208 * x801rsi) % 18446744073709551616, (x801m208 * x801rdx) % 18446744073709551616, (x801m210 * x801rdx) % 18446744073709551616, (x801m210 * x801rdx / 18446744073709551616) % 18446744073709551616, (x801m208 * x801r9) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L886
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x801rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x801rcx)
    · exact hB_x801rcx
    · first | exact hE_x801rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x801rbx)
    · exact hB_x801rbx
    · first | exact hE_x801rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x801rsi)
    · exact hB_x801rsi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x801r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x801r8)
    · exact hB_x801r8
    · first | exact hE_x801r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x801r9)
    · exact hB_x801r9
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
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x801m40
    · exact hB_x801m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x801m48
    · exact hB_x801m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x801m50
    · exact hB_x801m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x801m60
    · exact hB_x801m60
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x801m218
    · exact hB_x801m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x801m220
    · exact hB_x801m220
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
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
