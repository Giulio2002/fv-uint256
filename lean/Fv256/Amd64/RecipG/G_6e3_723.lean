import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_6e3_723 (s : State) (y3 : Nat) (x6e3rax x6e3rcx x6e3rdx x6e3rbx x6e3rsi x6e3rdi x6e3r8 x6e3r9 x6e3r10 x6e3r12 x6e3r15 x6e3m38 x6e3m68 x6e3m70 x6e3m98 x6e3ma0 x6e3ma8 x6e3m150 x6e3m158 x6e3m160 x6e3m168 x6e3m170 x6e3m178 x6e3m180 x6e3m188 x6e3m190 x6e3m198 x6e3m1a0 x6e3m1a8 x6e3m1b0 x6e3m1b8 x6e3m208 x6e3m210 x6e3m218 x6e3m220 : Nat) (S' : State) : Prop :=
  ∃ x723rdx x723rbx x723rsi x723r12 x723r13 x723r15, L723 s S' x6e3rax x6e3rcx x723rdx x723rbx x723rsi x6e3rdi x6e3r8 x6e3r9 x6e3r10 x723r12 x723r13 x723r15 x6e3m68 x6e3m70 x6e3m98 x6e3ma0 x6e3ma8 x6e3m150 x6e3m158 x6e3m160 x6e3m168 x6e3m170 x6e3m178 x6e3m180 x6e3m188 x6e3m190 x6e3m208 x6e3m210 x6e3m218 x6e3m220 ∧ x723rdx = (x6e3m38 + (x6e3m198 + x6e3rdx + (x6e3m1a8 + x6e3rsi + (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x723rbx = (x6e3m1a8 + x6e3rsi + (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x723rsi = (x6e3m198 + x6e3rdx + (x6e3m1a8 + x6e3rsi + (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x723r12 = (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) % 18446744073709551616 ∧ x723r13 = (x6e3m1b0 + x6e3r12) % 18446744073709551616 ∧ x723r15 = (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_6e3_723 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x6e3)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x6e3rax x6e3rcx x6e3rdx x6e3rbx x6e3rsi x6e3rdi x6e3r8 x6e3r9 x6e3r10 x6e3r12 x6e3r15 x6e3m38 x6e3m68 x6e3m70 x6e3m98 x6e3ma0 x6e3ma8 x6e3m150 x6e3m158 x6e3m160 x6e3m168 x6e3m170 x6e3m178 x6e3m180 x6e3m188 x6e3m190 x6e3m198 x6e3m1a0 x6e3m1a8 x6e3m1b0 x6e3m1b8 x6e3m208 x6e3m210 x6e3m218 x6e3m220 : Nat) (hL : L6e3 s S x6e3rax x6e3rcx x6e3rdx x6e3rbx x6e3rsi x6e3rdi x6e3r8 x6e3r9 x6e3r10 x6e3r12 x6e3r15 x6e3m38 x6e3m68 x6e3m70 x6e3m98 x6e3ma0 x6e3ma8 x6e3m150 x6e3m158 x6e3m160 x6e3m168 x6e3m170 x6e3m178 x6e3m180 x6e3m188 x6e3m190 x6e3m198 x6e3m1a0 x6e3m1a8 x6e3m1b0 x6e3m1b8 x6e3m208 x6e3m210 x6e3m218 x6e3m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x723)) S (P_6e3_723 s y3 x6e3rax x6e3rcx x6e3rdx x6e3rbx x6e3rsi x6e3rdi x6e3r8 x6e3r9 x6e3r10 x6e3r12 x6e3r15 x6e3m38 x6e3m68 x6e3m70 x6e3m98 x6e3ma0 x6e3ma8 x6e3m150 x6e3m158 x6e3m160 x6e3m168 x6e3m170 x6e3m178 x6e3m180 x6e3m188 x6e3m190 x6e3m198 x6e3m1a0 x6e3m1a8 x6e3m1b0 x6e3m1b8 x6e3m208 x6e3m210 x6e3m218 x6e3m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x6e3rax, hB_x6e3rax, hE_x6e3rcx, hB_x6e3rcx, hE_x6e3rdx, hB_x6e3rdx, hE_x6e3rbx, hB_x6e3rbx, hE_x6e3rsi, hB_x6e3rsi, hE_x6e3rdi, hB_x6e3rdi, hE_x6e3r8, hB_x6e3r8, hE_x6e3r9, hB_x6e3r9, hE_x6e3r10, hB_x6e3r10, hE_x6e3r12, hB_x6e3r12, hE_x6e3r15, hB_x6e3r15, hE_x6e3m38, hB_x6e3m38, hE_x6e3m68, hB_x6e3m68, hE_x6e3m70, hB_x6e3m70, hE_x6e3m98, hB_x6e3m98, hE_x6e3ma0, hB_x6e3ma0, hE_x6e3ma8, hB_x6e3ma8, hE_x6e3m150, hB_x6e3m150, hE_x6e3m158, hB_x6e3m158, hE_x6e3m160, hB_x6e3m160, hE_x6e3m168, hB_x6e3m168, hE_x6e3m170, hB_x6e3m170, hE_x6e3m178, hB_x6e3m178, hE_x6e3m180, hB_x6e3m180, hE_x6e3m188, hB_x6e3m188, hE_x6e3m190, hB_x6e3m190, hE_x6e3m198, hB_x6e3m198, hE_x6e3m1a0, hB_x6e3m1a0, hE_x6e3m1a8, hB_x6e3m1a8, hE_x6e3m1b0, hB_x6e3m1b0, hE_x6e3m1b8, hB_x6e3m1b8, hE_x6e3m208, hB_x6e3m208, hE_x6e3m210, hB_x6e3m210, hE_x6e3m218, hB_x6e3m218, hE_x6e3m220, hB_x6e3m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x6e3rax, hE_x6e3rcx, hE_x6e3rdx, hE_x6e3rbx, hE_x6e3rsi, hE_x6e3rdi, hE_x6e3r8, hE_x6e3r9, hE_x6e3r10, hE_x6e3r12, hE_x6e3r15, hE_x6e3m38, hE_x6e3m68, hE_x6e3m70, hE_x6e3m98, hE_x6e3ma0, hE_x6e3ma8, hE_x6e3m150, hE_x6e3m158, hE_x6e3m160, hE_x6e3m168, hE_x6e3m170, hE_x6e3m178, hE_x6e3m180, hE_x6e3m188, hE_x6e3m190, hE_x6e3m198, hE_x6e3m1a0, hE_x6e3m1a8, hE_x6e3m1b0, hE_x6e3m1b8, hE_x6e3m208, hE_x6e3m210, hE_x6e3m218, hE_x6e3m220, hsp4, Nat.mod_eq_of_lt hB_x6e3rax, Nat.mod_eq_of_lt hB_x6e3rcx, Nat.mod_eq_of_lt hB_x6e3rdx, Nat.mod_eq_of_lt hB_x6e3rbx, Nat.mod_eq_of_lt hB_x6e3rsi, Nat.mod_eq_of_lt hB_x6e3rdi, Nat.mod_eq_of_lt hB_x6e3r8, Nat.mod_eq_of_lt hB_x6e3r9, Nat.mod_eq_of_lt hB_x6e3r10, Nat.mod_eq_of_lt hB_x6e3r12, Nat.mod_eq_of_lt hB_x6e3r15, Nat.mod_eq_of_lt hB_x6e3m38, Nat.mod_eq_of_lt hB_x6e3m68, Nat.mod_eq_of_lt hB_x6e3m70, Nat.mod_eq_of_lt hB_x6e3m98, Nat.mod_eq_of_lt hB_x6e3ma0, Nat.mod_eq_of_lt hB_x6e3ma8, Nat.mod_eq_of_lt hB_x6e3m150, Nat.mod_eq_of_lt hB_x6e3m158, Nat.mod_eq_of_lt hB_x6e3m160, Nat.mod_eq_of_lt hB_x6e3m168, Nat.mod_eq_of_lt hB_x6e3m170, Nat.mod_eq_of_lt hB_x6e3m178, Nat.mod_eq_of_lt hB_x6e3m180, Nat.mod_eq_of_lt hB_x6e3m188, Nat.mod_eq_of_lt hB_x6e3m190, Nat.mod_eq_of_lt hB_x6e3m198, Nat.mod_eq_of_lt hB_x6e3m1a0, Nat.mod_eq_of_lt hB_x6e3m1a8, Nat.mod_eq_of_lt hB_x6e3m1b0, Nat.mod_eq_of_lt hB_x6e3m1b8, Nat.mod_eq_of_lt hB_x6e3m208, Nat.mod_eq_of_lt hB_x6e3m210, Nat.mod_eq_of_lt hB_x6e3m218, Nat.mod_eq_of_lt hB_x6e3m220]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_6e3_723
  refine ⟨(x6e3m38 + (x6e3m198 + x6e3rdx + (x6e3m1a8 + x6e3rsi + (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x6e3m1a8 + x6e3rsi + (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x6e3m198 + x6e3rdx + (x6e3m1a8 + x6e3rsi + (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) % 18446744073709551616, (x6e3m1b0 + x6e3r12) % 18446744073709551616, (x6e3m1a0 + x6e3rbx + (x6e3m1b8 + x6e3r15 + (x6e3m1b0 + x6e3r12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L723
    and_intros
    · first | exact hE_x6e3rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x6e3rax)
    · exact hB_x6e3rax
    · first | exact hE_x6e3rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x6e3rcx)
    · exact hB_x6e3rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x6e3rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x6e3rdi)
    · exact hB_x6e3rdi
    · first | exact hE_x6e3r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x6e3r8)
    · exact hB_x6e3r8
    · first | exact hE_x6e3r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x6e3r9)
    · exact hB_x6e3r9
    · first | exact hE_x6e3r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x6e3r10)
    · exact hB_x6e3r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m68
    · exact hB_x6e3m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m70
    · exact hB_x6e3m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m98
    · exact hB_x6e3m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3ma0
    · exact hB_x6e3ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3ma8
    · exact hB_x6e3ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m150
    · exact hB_x6e3m150
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m158
    · exact hB_x6e3m158
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m160
    · exact hB_x6e3m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m168
    · exact hB_x6e3m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m170
    · exact hB_x6e3m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m178
    · exact hB_x6e3m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m180
    · exact hB_x6e3m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m188
    · exact hB_x6e3m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m190
    · exact hB_x6e3m190
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m208
    · exact hB_x6e3m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m210
    · exact hB_x6e3m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m218
    · exact hB_x6e3m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x6e3m220
    · exact hB_x6e3m220
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
