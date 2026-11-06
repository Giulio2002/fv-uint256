import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_a49_a71 (s : State) (y3 : Nat) (xa49rax xa49rcx xa49rdx xa49rbx xa49rsi xa49rdi xa49r10 xa49r11 xa49r12 xa49r13 xa49r15 xa49m40 xa49m48 xa49m50 xa49m60 xa49mc0 xa49mc8 xa49m100 xa49m160 xa49m168 xa49m170 xa49m178 xa49m180 xa49m188 xa49m190 xa49m198 xa49m1a0 xa49m1a8 xa49m1b0 xa49m1b8 xa49m1c0 xa49m1c8 xa49m1d0 xa49m1d8 xa49m1e0 xa49m218 xa49m220 : Nat) (S' : State) : Prop :=
  ∃ xa71rdi xa71r9 xa71r10 xa71r11 xa71r15, La71 s S' xa49rax xa49rcx xa49rdx xa49rbx xa49rsi xa71rdi xa71r9 xa71r10 xa71r11 xa71r15 xa49m40 xa49m48 xa49m50 xa49m60 xa49mc0 xa49mc8 xa49m100 xa49m160 xa49m168 xa49m170 xa49m178 xa49m180 xa49m188 xa49m190 xa49m198 xa49m1a0 xa49m1a8 xa49m1b0 xa49m1b8 xa49m1c0 xa49m1c8 xa49m218 xa49m220 ∧ xa71rdi = (xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) % 18446744073709551616 ∧ xa71r9 = (xa49m1d8 + xa49rdi) % 18446744073709551616 ∧ xa71r10 = (xa49m1d0 + xa49r13 + (xa49r11 + xa49r12 + (xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xa71r11 = (xa49r11 + xa49r12 + (xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xa71r15 = (xa49r15 + (xa49m1d0 + xa49r13 + (xa49r11 + xa49r12 + (xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_a49_a71 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xa49)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xa49rax xa49rcx xa49rdx xa49rbx xa49rsi xa49rdi xa49r10 xa49r11 xa49r12 xa49r13 xa49r15 xa49m40 xa49m48 xa49m50 xa49m60 xa49mc0 xa49mc8 xa49m100 xa49m160 xa49m168 xa49m170 xa49m178 xa49m180 xa49m188 xa49m190 xa49m198 xa49m1a0 xa49m1a8 xa49m1b0 xa49m1b8 xa49m1c0 xa49m1c8 xa49m1d0 xa49m1d8 xa49m1e0 xa49m218 xa49m220 : Nat) (hL : La49 s S xa49rax xa49rcx xa49rdx xa49rbx xa49rsi xa49rdi xa49r10 xa49r11 xa49r12 xa49r13 xa49r15 xa49m40 xa49m48 xa49m50 xa49m60 xa49mc0 xa49mc8 xa49m100 xa49m160 xa49m168 xa49m170 xa49m178 xa49m180 xa49m188 xa49m190 xa49m198 xa49m1a0 xa49m1a8 xa49m1b0 xa49m1b8 xa49m1c0 xa49m1c8 xa49m1d0 xa49m1d8 xa49m1e0 xa49m218 xa49m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xa71)) S (P_a49_a71 s y3 xa49rax xa49rcx xa49rdx xa49rbx xa49rsi xa49rdi xa49r10 xa49r11 xa49r12 xa49r13 xa49r15 xa49m40 xa49m48 xa49m50 xa49m60 xa49mc0 xa49mc8 xa49m100 xa49m160 xa49m168 xa49m170 xa49m178 xa49m180 xa49m188 xa49m190 xa49m198 xa49m1a0 xa49m1a8 xa49m1b0 xa49m1b8 xa49m1c0 xa49m1c8 xa49m1d0 xa49m1d8 xa49m1e0 xa49m218 xa49m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xa49rax, hB_xa49rax, hE_xa49rcx, hB_xa49rcx, hE_xa49rdx, hB_xa49rdx, hE_xa49rbx, hB_xa49rbx, hE_xa49rsi, hB_xa49rsi, hE_xa49rdi, hB_xa49rdi, hE_xa49r10, hB_xa49r10, hE_xa49r11, hB_xa49r11, hE_xa49r12, hB_xa49r12, hE_xa49r13, hB_xa49r13, hE_xa49r15, hB_xa49r15, hE_xa49m40, hB_xa49m40, hE_xa49m48, hB_xa49m48, hE_xa49m50, hB_xa49m50, hE_xa49m60, hB_xa49m60, hE_xa49mc0, hB_xa49mc0, hE_xa49mc8, hB_xa49mc8, hE_xa49m100, hB_xa49m100, hE_xa49m160, hB_xa49m160, hE_xa49m168, hB_xa49m168, hE_xa49m170, hB_xa49m170, hE_xa49m178, hB_xa49m178, hE_xa49m180, hB_xa49m180, hE_xa49m188, hB_xa49m188, hE_xa49m190, hB_xa49m190, hE_xa49m198, hB_xa49m198, hE_xa49m1a0, hB_xa49m1a0, hE_xa49m1a8, hB_xa49m1a8, hE_xa49m1b0, hB_xa49m1b0, hE_xa49m1b8, hB_xa49m1b8, hE_xa49m1c0, hB_xa49m1c0, hE_xa49m1c8, hB_xa49m1c8, hE_xa49m1d0, hB_xa49m1d0, hE_xa49m1d8, hB_xa49m1d8, hE_xa49m1e0, hB_xa49m1e0, hE_xa49m218, hB_xa49m218, hE_xa49m220, hB_xa49m220⟩ := hL
  janus64_run [Util.readLE_32, hE_xa49rax, hE_xa49rcx, hE_xa49rdx, hE_xa49rbx, hE_xa49rsi, hE_xa49rdi, hE_xa49r10, hE_xa49r11, hE_xa49r12, hE_xa49r13, hE_xa49r15, hE_xa49m40, hE_xa49m48, hE_xa49m50, hE_xa49m60, hE_xa49mc0, hE_xa49mc8, hE_xa49m100, hE_xa49m160, hE_xa49m168, hE_xa49m170, hE_xa49m178, hE_xa49m180, hE_xa49m188, hE_xa49m190, hE_xa49m198, hE_xa49m1a0, hE_xa49m1a8, hE_xa49m1b0, hE_xa49m1b8, hE_xa49m1c0, hE_xa49m1c8, hE_xa49m1d0, hE_xa49m1d8, hE_xa49m1e0, hE_xa49m218, hE_xa49m220, hsp4, Nat.mod_eq_of_lt hB_xa49rax, Nat.mod_eq_of_lt hB_xa49rcx, Nat.mod_eq_of_lt hB_xa49rdx, Nat.mod_eq_of_lt hB_xa49rbx, Nat.mod_eq_of_lt hB_xa49rsi, Nat.mod_eq_of_lt hB_xa49rdi, Nat.mod_eq_of_lt hB_xa49r10, Nat.mod_eq_of_lt hB_xa49r11, Nat.mod_eq_of_lt hB_xa49r12, Nat.mod_eq_of_lt hB_xa49r13, Nat.mod_eq_of_lt hB_xa49r15, Nat.mod_eq_of_lt hB_xa49m40, Nat.mod_eq_of_lt hB_xa49m48, Nat.mod_eq_of_lt hB_xa49m50, Nat.mod_eq_of_lt hB_xa49m60, Nat.mod_eq_of_lt hB_xa49mc0, Nat.mod_eq_of_lt hB_xa49mc8, Nat.mod_eq_of_lt hB_xa49m100, Nat.mod_eq_of_lt hB_xa49m160, Nat.mod_eq_of_lt hB_xa49m168, Nat.mod_eq_of_lt hB_xa49m170, Nat.mod_eq_of_lt hB_xa49m178, Nat.mod_eq_of_lt hB_xa49m180, Nat.mod_eq_of_lt hB_xa49m188, Nat.mod_eq_of_lt hB_xa49m190, Nat.mod_eq_of_lt hB_xa49m198, Nat.mod_eq_of_lt hB_xa49m1a0, Nat.mod_eq_of_lt hB_xa49m1a8, Nat.mod_eq_of_lt hB_xa49m1b0, Nat.mod_eq_of_lt hB_xa49m1b8, Nat.mod_eq_of_lt hB_xa49m1c0, Nat.mod_eq_of_lt hB_xa49m1c8, Nat.mod_eq_of_lt hB_xa49m1d0, Nat.mod_eq_of_lt hB_xa49m1d8, Nat.mod_eq_of_lt hB_xa49m1e0, Nat.mod_eq_of_lt hB_xa49m218, Nat.mod_eq_of_lt hB_xa49m220]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_a49_a71
  refine ⟨(xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) % 18446744073709551616, (xa49m1d8 + xa49rdi) % 18446744073709551616, (xa49m1d0 + xa49r13 + (xa49r11 + xa49r12 + (xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa49r11 + xa49r12 + (xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa49r15 + (xa49m1d0 + xa49r13 + (xa49r11 + xa49r12 + (xa49m1e0 + xa49r10 + (xa49m1d8 + xa49rdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold La71
    and_intros
    · first | exact hE_xa49rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa49rax)
    · exact hB_xa49rax
    · first | exact hE_xa49rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa49rcx)
    · exact hB_xa49rcx
    · first | exact hE_xa49rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa49rdx)
    · exact hB_xa49rdx
    · first | exact hE_xa49rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa49rbx)
    · exact hB_xa49rbx
    · first | exact hE_xa49rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa49rsi)
    · exact hB_xa49rsi
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
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m40
    · exact hB_xa49m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m48
    · exact hB_xa49m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m50
    · exact hB_xa49m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m60
    · exact hB_xa49m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49mc0
    · exact hB_xa49mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49mc8
    · exact hB_xa49mc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m100
    · exact hB_xa49m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m160
    · exact hB_xa49m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m168
    · exact hB_xa49m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m170
    · exact hB_xa49m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m178
    · exact hB_xa49m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m180
    · exact hB_xa49m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m188
    · exact hB_xa49m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m190
    · exact hB_xa49m190
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m198
    · exact hB_xa49m198
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m1a0
    · exact hB_xa49m1a0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m1a8
    · exact hB_xa49m1a8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m1b0
    · exact hB_xa49m1b0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m1b8
    · exact hB_xa49m1b8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m1c0
    · exact hB_xa49m1c0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m1c8
    · exact hB_xa49m1c8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m218
    · exact hB_xa49m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa49m220
    · exact hB_xa49m220
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
