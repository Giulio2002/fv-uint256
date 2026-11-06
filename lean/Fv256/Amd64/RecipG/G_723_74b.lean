import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_723_74b (s : State) (y3 : Nat) (x723rax x723rcx x723rdx x723rbx x723rsi x723rdi x723r8 x723r9 x723r10 x723r12 x723r13 x723r15 x723m68 x723m70 x723m98 x723ma0 x723ma8 x723m150 x723m158 x723m160 x723m168 x723m170 x723m178 x723m180 x723m188 x723m190 x723m208 x723m210 x723m218 x723m220 : Nat) (S' : State) : Prop :=
  ∃ x74brdx x74br10 x74br11 x74br12 x74br15, L74b s S' x723rax x723rcx x74brdx x723rdi x723r8 x723r9 x74br10 x74br11 x74br12 x723r13 x74br15 x723m68 x723m70 x723m98 x723ma0 x723ma8 x723m150 x723m158 x723m160 x723m168 x723m170 x723m178 x723m208 x723m210 x723m218 x723m220 ∧ x74brdx = (x723rdx + (x723r10 + x723rsi + (x723m180 + x723rbx + (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x74br10 = (x723r10 + x723rsi + (x723m180 + x723rbx + (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x74br11 = (x723m188 + x723r12) % 18446744073709551616 ∧ x74br12 = (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) % 18446744073709551616 ∧ x74br15 = (x723m180 + x723rbx + (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_723_74b {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x723)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x723rax x723rcx x723rdx x723rbx x723rsi x723rdi x723r8 x723r9 x723r10 x723r12 x723r13 x723r15 x723m68 x723m70 x723m98 x723ma0 x723ma8 x723m150 x723m158 x723m160 x723m168 x723m170 x723m178 x723m180 x723m188 x723m190 x723m208 x723m210 x723m218 x723m220 : Nat) (hL : L723 s S x723rax x723rcx x723rdx x723rbx x723rsi x723rdi x723r8 x723r9 x723r10 x723r12 x723r13 x723r15 x723m68 x723m70 x723m98 x723ma0 x723ma8 x723m150 x723m158 x723m160 x723m168 x723m170 x723m178 x723m180 x723m188 x723m190 x723m208 x723m210 x723m218 x723m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x74b)) S (P_723_74b s y3 x723rax x723rcx x723rdx x723rbx x723rsi x723rdi x723r8 x723r9 x723r10 x723r12 x723r13 x723r15 x723m68 x723m70 x723m98 x723ma0 x723ma8 x723m150 x723m158 x723m160 x723m168 x723m170 x723m178 x723m180 x723m188 x723m190 x723m208 x723m210 x723m218 x723m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x723rax, hB_x723rax, hE_x723rcx, hB_x723rcx, hE_x723rdx, hB_x723rdx, hE_x723rbx, hB_x723rbx, hE_x723rsi, hB_x723rsi, hE_x723rdi, hB_x723rdi, hE_x723r8, hB_x723r8, hE_x723r9, hB_x723r9, hE_x723r10, hB_x723r10, hE_x723r12, hB_x723r12, hE_x723r13, hB_x723r13, hE_x723r15, hB_x723r15, hE_x723m68, hB_x723m68, hE_x723m70, hB_x723m70, hE_x723m98, hB_x723m98, hE_x723ma0, hB_x723ma0, hE_x723ma8, hB_x723ma8, hE_x723m150, hB_x723m150, hE_x723m158, hB_x723m158, hE_x723m160, hB_x723m160, hE_x723m168, hB_x723m168, hE_x723m170, hB_x723m170, hE_x723m178, hB_x723m178, hE_x723m180, hB_x723m180, hE_x723m188, hB_x723m188, hE_x723m190, hB_x723m190, hE_x723m208, hB_x723m208, hE_x723m210, hB_x723m210, hE_x723m218, hB_x723m218, hE_x723m220, hB_x723m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x723rax, hE_x723rcx, hE_x723rdx, hE_x723rbx, hE_x723rsi, hE_x723rdi, hE_x723r8, hE_x723r9, hE_x723r10, hE_x723r12, hE_x723r13, hE_x723r15, hE_x723m68, hE_x723m70, hE_x723m98, hE_x723ma0, hE_x723ma8, hE_x723m150, hE_x723m158, hE_x723m160, hE_x723m168, hE_x723m170, hE_x723m178, hE_x723m180, hE_x723m188, hE_x723m190, hE_x723m208, hE_x723m210, hE_x723m218, hE_x723m220, hsp4, Nat.mod_eq_of_lt hB_x723rax, Nat.mod_eq_of_lt hB_x723rcx, Nat.mod_eq_of_lt hB_x723rdx, Nat.mod_eq_of_lt hB_x723rbx, Nat.mod_eq_of_lt hB_x723rsi, Nat.mod_eq_of_lt hB_x723rdi, Nat.mod_eq_of_lt hB_x723r8, Nat.mod_eq_of_lt hB_x723r9, Nat.mod_eq_of_lt hB_x723r10, Nat.mod_eq_of_lt hB_x723r12, Nat.mod_eq_of_lt hB_x723r13, Nat.mod_eq_of_lt hB_x723r15, Nat.mod_eq_of_lt hB_x723m68, Nat.mod_eq_of_lt hB_x723m70, Nat.mod_eq_of_lt hB_x723m98, Nat.mod_eq_of_lt hB_x723ma0, Nat.mod_eq_of_lt hB_x723ma8, Nat.mod_eq_of_lt hB_x723m150, Nat.mod_eq_of_lt hB_x723m158, Nat.mod_eq_of_lt hB_x723m160, Nat.mod_eq_of_lt hB_x723m168, Nat.mod_eq_of_lt hB_x723m170, Nat.mod_eq_of_lt hB_x723m178, Nat.mod_eq_of_lt hB_x723m180, Nat.mod_eq_of_lt hB_x723m188, Nat.mod_eq_of_lt hB_x723m190, Nat.mod_eq_of_lt hB_x723m208, Nat.mod_eq_of_lt hB_x723m210, Nat.mod_eq_of_lt hB_x723m218, Nat.mod_eq_of_lt hB_x723m220]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_723_74b
  refine ⟨(x723rdx + (x723r10 + x723rsi + (x723m180 + x723rbx + (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x723r10 + x723rsi + (x723m180 + x723rbx + (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x723m188 + x723r12) % 18446744073709551616, (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) % 18446744073709551616, (x723m180 + x723rbx + (x723m190 + x723r15 + (x723m188 + x723r12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L74b
    and_intros
    · first | exact hE_x723rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x723rax)
    · exact hB_x723rax
    · first | exact hE_x723rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x723rcx)
    · exact hB_x723rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x723rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x723rdi)
    · exact hB_x723rdi
    · first | exact hE_x723r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x723r8)
    · exact hB_x723r8
    · first | exact hE_x723r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x723r9)
    · exact hB_x723r9
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x723r13 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x723r13)
    · exact hB_x723r13
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m68
    · exact hB_x723m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m70
    · exact hB_x723m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m98
    · exact hB_x723m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723ma0
    · exact hB_x723ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723ma8
    · exact hB_x723ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m150
    · exact hB_x723m150
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m158
    · exact hB_x723m158
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m160
    · exact hB_x723m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m168
    · exact hB_x723m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m170
    · exact hB_x723m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m178
    · exact hB_x723m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m208
    · exact hB_x723m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m210
    · exact hB_x723m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m218
    · exact hB_x723m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x723m220
    · exact hB_x723m220
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
