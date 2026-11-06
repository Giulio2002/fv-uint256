import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_502_549 (s : State) (y3 : Nat) (x502rcx x502rbx x502rsi x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x502m98 x502ma0 x502ma8 x502m208 x502m210 x502m218 x502m220 : Nat) (S' : State) : Prop :=
  ∃ x549rax x549r13 x549r15 x549m48 x549m50 x549m58 x549m1f8 x549m200, L549 s S' x549rax x502rcx x502rbx x502rsi x502rdi x502r8 x502r9 x502r10 x549r13 x549r15 x549m48 x549m50 x549m58 x502m68 x502m70 x502m98 x502ma0 x502ma8 x549m1f8 x549m200 x502m208 x502m210 x502m218 x502m220 ∧ x549rax = x502r8 % 18446744073709551616 ∧ x549r13 = x502m210 % 18446744073709551616 ∧ x549r15 = (x502m208 * x502r8) % 18446744073709551616 ∧ x549m48 = (x502m208 * x502r9 / 18446744073709551616) % 18446744073709551616 ∧ x549m50 = (x502m208 * x502r9) % 18446744073709551616 ∧ x549m58 = (x502m208 * x502r8 / 18446744073709551616) % 18446744073709551616 ∧ x549m1f8 = (x502m208 * x502rbx) % 18446744073709551616 ∧ x549m200 = (x502m208 * x502rbx / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_502_549 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x502)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x502rcx x502rbx x502rsi x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x502m98 x502ma0 x502ma8 x502m208 x502m210 x502m218 x502m220 : Nat) (hL : L502 s S x502rcx x502rbx x502rsi x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x502m98 x502ma0 x502ma8 x502m208 x502m210 x502m218 x502m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x549)) S (P_502_549 s y3 x502rcx x502rbx x502rsi x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x502m98 x502ma0 x502ma8 x502m208 x502m210 x502m218 x502m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x502rcx, hB_x502rcx, hE_x502rbx, hB_x502rbx, hE_x502rsi, hB_x502rsi, hE_x502rdi, hB_x502rdi, hE_x502r8, hB_x502r8, hE_x502r9, hB_x502r9, hE_x502r10, hB_x502r10, hE_x502m68, hB_x502m68, hE_x502m70, hB_x502m70, hE_x502m98, hB_x502m98, hE_x502ma0, hB_x502ma0, hE_x502ma8, hB_x502ma8, hE_x502m208, hB_x502m208, hE_x502m210, hB_x502m210, hE_x502m218, hB_x502m218, hE_x502m220, hB_x502m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x502rcx, hE_x502rbx, hE_x502rsi, hE_x502rdi, hE_x502r8, hE_x502r9, hE_x502r10, hE_x502m68, hE_x502m70, hE_x502m98, hE_x502ma0, hE_x502ma8, hE_x502m208, hE_x502m210, hE_x502m218, hE_x502m220, hsp4, Nat.mod_eq_of_lt hB_x502rcx, Nat.mod_eq_of_lt hB_x502rbx, Nat.mod_eq_of_lt hB_x502rsi, Nat.mod_eq_of_lt hB_x502rdi, Nat.mod_eq_of_lt hB_x502r8, Nat.mod_eq_of_lt hB_x502r9, Nat.mod_eq_of_lt hB_x502r10, Nat.mod_eq_of_lt hB_x502m68, Nat.mod_eq_of_lt hB_x502m70, Nat.mod_eq_of_lt hB_x502m98, Nat.mod_eq_of_lt hB_x502ma0, Nat.mod_eq_of_lt hB_x502ma8, Nat.mod_eq_of_lt hB_x502m208, Nat.mod_eq_of_lt hB_x502m210, Nat.mod_eq_of_lt hB_x502m218, Nat.mod_eq_of_lt hB_x502m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_502_549
  refine ⟨x502r8 % 18446744073709551616, x502m210 % 18446744073709551616, (x502m208 * x502r8) % 18446744073709551616, (x502m208 * x502r9 / 18446744073709551616) % 18446744073709551616, (x502m208 * x502r9) % 18446744073709551616, (x502m208 * x502r8 / 18446744073709551616) % 18446744073709551616, (x502m208 * x502rbx) % 18446744073709551616, (x502m208 * x502rbx / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L549
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x502rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x502rcx)
    · exact hB_x502rcx
    · first | exact hE_x502rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x502rbx)
    · exact hB_x502rbx
    · first | exact hE_x502rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x502rsi)
    · exact hB_x502rsi
    · first | exact hE_x502rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x502rdi)
    · exact hB_x502rdi
    · first | exact hE_x502r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x502r8)
    · exact hB_x502r8
    · first | exact hE_x502r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x502r9)
    · exact hB_x502r9
    · first | exact hE_x502r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x502r10)
    · exact hB_x502r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502m68
    · exact hB_x502m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502m70
    · exact hB_x502m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502m98
    · exact hB_x502m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502ma0
    · exact hB_x502ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502ma8
    · exact hB_x502ma8
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502m208
    · exact hB_x502m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502m210
    · exact hB_x502m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502m218
    · exact hB_x502m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x502m220
    · exact hB_x502m220
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
