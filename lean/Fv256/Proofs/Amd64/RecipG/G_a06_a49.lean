import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_a06_a49 (s : State) (y3 : Nat) (xa06rax xa06rcx xa06rdx xa06rbx xa06rdi xa06r10 xa06r11 xa06r12 xa06r13 xa06r15 xa06m40 xa06m48 xa06m50 xa06m60 xa06mc0 xa06mc8 xa06md0 xa06m100 xa06m160 xa06m168 xa06m170 xa06m178 xa06m180 xa06m188 xa06m190 xa06m198 xa06m1a0 xa06m1a8 xa06m1b0 xa06m1b8 xa06m1c0 xa06m1c8 xa06m1d0 xa06m1d8 xa06m1e0 xa06m1e8 xa06m1f0 xa06m1f8 xa06m200 xa06m210 xa06m218 xa06m220 : Nat) (S' : State) : Prop :=
  ∃ xa49rsi xa49rdi xa49r10 xa49r12 xa49r13 xa49r15, La49 s S' xa06rax xa06rcx xa06rdx xa06rbx xa49rsi xa49rdi xa49r10 xa06r11 xa49r12 xa49r13 xa49r15 xa06m40 xa06m48 xa06m50 xa06m60 xa06mc0 xa06mc8 xa06m100 xa06m160 xa06m168 xa06m170 xa06m178 xa06m180 xa06m188 xa06m190 xa06m198 xa06m1a0 xa06m1a8 xa06m1b0 xa06m1b8 xa06m1c0 xa06m1c8 xa06m1d0 xa06m1d8 xa06m1e0 xa06m218 xa06m220 ∧ xa49rsi = (xa06m1f8 + xa06rdi) % 18446744073709551616 ∧ xa49rdi = (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) % 18446744073709551616 ∧ xa49r10 = (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xa49r12 = (xa06m210 + xa06r13 + (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xa49r13 = (xa06m1e8 + xa06r15 + (xa06m210 + xa06r13 + (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xa49r15 = (xa06md0 + (xa06m1e8 + xa06r15 + (xa06m210 + xa06r13 + (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_a06_a49 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xa06)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xa06rax xa06rcx xa06rdx xa06rbx xa06rdi xa06r10 xa06r11 xa06r12 xa06r13 xa06r15 xa06m40 xa06m48 xa06m50 xa06m60 xa06mc0 xa06mc8 xa06md0 xa06m100 xa06m160 xa06m168 xa06m170 xa06m178 xa06m180 xa06m188 xa06m190 xa06m198 xa06m1a0 xa06m1a8 xa06m1b0 xa06m1b8 xa06m1c0 xa06m1c8 xa06m1d0 xa06m1d8 xa06m1e0 xa06m1e8 xa06m1f0 xa06m1f8 xa06m200 xa06m210 xa06m218 xa06m220 : Nat) (hL : La06 s S xa06rax xa06rcx xa06rdx xa06rbx xa06rdi xa06r10 xa06r11 xa06r12 xa06r13 xa06r15 xa06m40 xa06m48 xa06m50 xa06m60 xa06mc0 xa06mc8 xa06md0 xa06m100 xa06m160 xa06m168 xa06m170 xa06m178 xa06m180 xa06m188 xa06m190 xa06m198 xa06m1a0 xa06m1a8 xa06m1b0 xa06m1b8 xa06m1c0 xa06m1c8 xa06m1d0 xa06m1d8 xa06m1e0 xa06m1e8 xa06m1f0 xa06m1f8 xa06m200 xa06m210 xa06m218 xa06m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xa49)) S (P_a06_a49 s y3 xa06rax xa06rcx xa06rdx xa06rbx xa06rdi xa06r10 xa06r11 xa06r12 xa06r13 xa06r15 xa06m40 xa06m48 xa06m50 xa06m60 xa06mc0 xa06mc8 xa06md0 xa06m100 xa06m160 xa06m168 xa06m170 xa06m178 xa06m180 xa06m188 xa06m190 xa06m198 xa06m1a0 xa06m1a8 xa06m1b0 xa06m1b8 xa06m1c0 xa06m1c8 xa06m1d0 xa06m1d8 xa06m1e0 xa06m1e8 xa06m1f0 xa06m1f8 xa06m200 xa06m210 xa06m218 xa06m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xa06rax, hB_xa06rax, hE_xa06rcx, hB_xa06rcx, hE_xa06rdx, hB_xa06rdx, hE_xa06rbx, hB_xa06rbx, hE_xa06rdi, hB_xa06rdi, hE_xa06r10, hB_xa06r10, hE_xa06r11, hB_xa06r11, hE_xa06r12, hB_xa06r12, hE_xa06r13, hB_xa06r13, hE_xa06r15, hB_xa06r15, hE_xa06m40, hB_xa06m40, hE_xa06m48, hB_xa06m48, hE_xa06m50, hB_xa06m50, hE_xa06m60, hB_xa06m60, hE_xa06mc0, hB_xa06mc0, hE_xa06mc8, hB_xa06mc8, hE_xa06md0, hB_xa06md0, hE_xa06m100, hB_xa06m100, hE_xa06m160, hB_xa06m160, hE_xa06m168, hB_xa06m168, hE_xa06m170, hB_xa06m170, hE_xa06m178, hB_xa06m178, hE_xa06m180, hB_xa06m180, hE_xa06m188, hB_xa06m188, hE_xa06m190, hB_xa06m190, hE_xa06m198, hB_xa06m198, hE_xa06m1a0, hB_xa06m1a0, hE_xa06m1a8, hB_xa06m1a8, hE_xa06m1b0, hB_xa06m1b0, hE_xa06m1b8, hB_xa06m1b8, hE_xa06m1c0, hB_xa06m1c0, hE_xa06m1c8, hB_xa06m1c8, hE_xa06m1d0, hB_xa06m1d0, hE_xa06m1d8, hB_xa06m1d8, hE_xa06m1e0, hB_xa06m1e0, hE_xa06m1e8, hB_xa06m1e8, hE_xa06m1f0, hB_xa06m1f0, hE_xa06m1f8, hB_xa06m1f8, hE_xa06m200, hB_xa06m200, hE_xa06m210, hB_xa06m210, hE_xa06m218, hB_xa06m218, hE_xa06m220, hB_xa06m220⟩ := hL
  janus64_run [Util.readLE_32, hE_xa06rax, hE_xa06rcx, hE_xa06rdx, hE_xa06rbx, hE_xa06rdi, hE_xa06r10, hE_xa06r11, hE_xa06r12, hE_xa06r13, hE_xa06r15, hE_xa06m40, hE_xa06m48, hE_xa06m50, hE_xa06m60, hE_xa06mc0, hE_xa06mc8, hE_xa06md0, hE_xa06m100, hE_xa06m160, hE_xa06m168, hE_xa06m170, hE_xa06m178, hE_xa06m180, hE_xa06m188, hE_xa06m190, hE_xa06m198, hE_xa06m1a0, hE_xa06m1a8, hE_xa06m1b0, hE_xa06m1b8, hE_xa06m1c0, hE_xa06m1c8, hE_xa06m1d0, hE_xa06m1d8, hE_xa06m1e0, hE_xa06m1e8, hE_xa06m1f0, hE_xa06m1f8, hE_xa06m200, hE_xa06m210, hE_xa06m218, hE_xa06m220, hsp4, Nat.mod_eq_of_lt hB_xa06rax, Nat.mod_eq_of_lt hB_xa06rcx, Nat.mod_eq_of_lt hB_xa06rdx, Nat.mod_eq_of_lt hB_xa06rbx, Nat.mod_eq_of_lt hB_xa06rdi, Nat.mod_eq_of_lt hB_xa06r10, Nat.mod_eq_of_lt hB_xa06r11, Nat.mod_eq_of_lt hB_xa06r12, Nat.mod_eq_of_lt hB_xa06r13, Nat.mod_eq_of_lt hB_xa06r15, Nat.mod_eq_of_lt hB_xa06m40, Nat.mod_eq_of_lt hB_xa06m48, Nat.mod_eq_of_lt hB_xa06m50, Nat.mod_eq_of_lt hB_xa06m60, Nat.mod_eq_of_lt hB_xa06mc0, Nat.mod_eq_of_lt hB_xa06mc8, Nat.mod_eq_of_lt hB_xa06md0, Nat.mod_eq_of_lt hB_xa06m100, Nat.mod_eq_of_lt hB_xa06m160, Nat.mod_eq_of_lt hB_xa06m168, Nat.mod_eq_of_lt hB_xa06m170, Nat.mod_eq_of_lt hB_xa06m178, Nat.mod_eq_of_lt hB_xa06m180, Nat.mod_eq_of_lt hB_xa06m188, Nat.mod_eq_of_lt hB_xa06m190, Nat.mod_eq_of_lt hB_xa06m198, Nat.mod_eq_of_lt hB_xa06m1a0, Nat.mod_eq_of_lt hB_xa06m1a8, Nat.mod_eq_of_lt hB_xa06m1b0, Nat.mod_eq_of_lt hB_xa06m1b8, Nat.mod_eq_of_lt hB_xa06m1c0, Nat.mod_eq_of_lt hB_xa06m1c8, Nat.mod_eq_of_lt hB_xa06m1d0, Nat.mod_eq_of_lt hB_xa06m1d8, Nat.mod_eq_of_lt hB_xa06m1e0, Nat.mod_eq_of_lt hB_xa06m1e8, Nat.mod_eq_of_lt hB_xa06m1f0, Nat.mod_eq_of_lt hB_xa06m1f8, Nat.mod_eq_of_lt hB_xa06m200, Nat.mod_eq_of_lt hB_xa06m210, Nat.mod_eq_of_lt hB_xa06m218, Nat.mod_eq_of_lt hB_xa06m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_a06_a49
  refine ⟨(xa06m1f8 + xa06rdi) % 18446744073709551616, (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) % 18446744073709551616, (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa06m210 + xa06r13 + (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa06m1e8 + xa06r15 + (xa06m210 + xa06r13 + (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa06md0 + (xa06m1e8 + xa06r15 + (xa06m210 + xa06r13 + (xa06m1f0 + xa06r12 + (xa06m200 + xa06r10 + (xa06m1f8 + xa06rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold La49
    and_intros
    · first | exact hE_xa06rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa06rax)
    · exact hB_xa06rax
    · first | exact hE_xa06rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa06rcx)
    · exact hB_xa06rcx
    · first | exact hE_xa06rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa06rdx)
    · exact hB_xa06rdx
    · first | exact hE_xa06rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa06rbx)
    · exact hB_xa06rbx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_xa06r11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa06r11)
    · exact hB_xa06r11
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m40
    · exact hB_xa06m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m48
    · exact hB_xa06m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m50
    · exact hB_xa06m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m60
    · exact hB_xa06m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06mc0
    · exact hB_xa06mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06mc8
    · exact hB_xa06mc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m100
    · exact hB_xa06m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m160
    · exact hB_xa06m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m168
    · exact hB_xa06m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m170
    · exact hB_xa06m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m178
    · exact hB_xa06m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m180
    · exact hB_xa06m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m188
    · exact hB_xa06m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m190
    · exact hB_xa06m190
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m198
    · exact hB_xa06m198
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1a0
    · exact hB_xa06m1a0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1a8
    · exact hB_xa06m1a8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1b0
    · exact hB_xa06m1b0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1b8
    · exact hB_xa06m1b8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1c0
    · exact hB_xa06m1c0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1c8
    · exact hB_xa06m1c8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1d0
    · exact hB_xa06m1d0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1d8
    · exact hB_xa06m1d8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m1e0
    · exact hB_xa06m1e0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m218
    · exact hB_xa06m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa06m220
    · exact hB_xa06m220
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
