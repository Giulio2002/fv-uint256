import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_a71_ab4 (s : State) (y3 : Nat) (xa71rax xa71rcx xa71rdx xa71rbx xa71rsi xa71rdi xa71r9 xa71r10 xa71r11 xa71r15 xa71m40 xa71m48 xa71m50 xa71m60 xa71mc0 xa71mc8 xa71m100 xa71m160 xa71m168 xa71m170 xa71m178 xa71m180 xa71m188 xa71m190 xa71m198 xa71m1a0 xa71m1a8 xa71m1b0 xa71m1b8 xa71m1c0 xa71m1c8 xa71m218 xa71m220 : Nat) (S' : State) : Prop :=
  ∃ xab4rdi xab4r9 xab4r10 xab4r11 xab4r12 xab4r13, Lab4 s S' xa71rax xa71rcx xa71rdx xa71rbx xa71rsi xab4rdi xab4r9 xab4r10 xab4r11 xab4r12 xab4r13 xa71m40 xa71m48 xa71m50 xa71m60 xa71mc0 xa71m100 xa71m160 xa71m168 xa71m170 xa71m178 xa71m180 xa71m188 xa71m190 xa71m198 xa71m1a0 xa71m218 xa71m220 ∧ xab4rdi = (xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xab4r9 = (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) % 18446744073709551616 ∧ xab4r10 = (xa71m1a8 + xa71r15 + (xa71m1b8 + xa71r10 + (xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xab4r11 = (xa71m1b8 + xa71r10 + (xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xab4r12 = (xa71m1c0 + xa71r9) % 18446744073709551616 ∧ xab4r13 = (xa71mc8 + (xa71m1a8 + xa71r15 + (xa71m1b8 + xa71r10 + (xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_a71_ab4 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xa71)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xa71rax xa71rcx xa71rdx xa71rbx xa71rsi xa71rdi xa71r9 xa71r10 xa71r11 xa71r15 xa71m40 xa71m48 xa71m50 xa71m60 xa71mc0 xa71mc8 xa71m100 xa71m160 xa71m168 xa71m170 xa71m178 xa71m180 xa71m188 xa71m190 xa71m198 xa71m1a0 xa71m1a8 xa71m1b0 xa71m1b8 xa71m1c0 xa71m1c8 xa71m218 xa71m220 : Nat) (hL : La71 s S xa71rax xa71rcx xa71rdx xa71rbx xa71rsi xa71rdi xa71r9 xa71r10 xa71r11 xa71r15 xa71m40 xa71m48 xa71m50 xa71m60 xa71mc0 xa71mc8 xa71m100 xa71m160 xa71m168 xa71m170 xa71m178 xa71m180 xa71m188 xa71m190 xa71m198 xa71m1a0 xa71m1a8 xa71m1b0 xa71m1b8 xa71m1c0 xa71m1c8 xa71m218 xa71m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xab4)) S (P_a71_ab4 s y3 xa71rax xa71rcx xa71rdx xa71rbx xa71rsi xa71rdi xa71r9 xa71r10 xa71r11 xa71r15 xa71m40 xa71m48 xa71m50 xa71m60 xa71mc0 xa71mc8 xa71m100 xa71m160 xa71m168 xa71m170 xa71m178 xa71m180 xa71m188 xa71m190 xa71m198 xa71m1a0 xa71m1a8 xa71m1b0 xa71m1b8 xa71m1c0 xa71m1c8 xa71m218 xa71m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xa71rax, hB_xa71rax, hE_xa71rcx, hB_xa71rcx, hE_xa71rdx, hB_xa71rdx, hE_xa71rbx, hB_xa71rbx, hE_xa71rsi, hB_xa71rsi, hE_xa71rdi, hB_xa71rdi, hE_xa71r9, hB_xa71r9, hE_xa71r10, hB_xa71r10, hE_xa71r11, hB_xa71r11, hE_xa71r15, hB_xa71r15, hE_xa71m40, hB_xa71m40, hE_xa71m48, hB_xa71m48, hE_xa71m50, hB_xa71m50, hE_xa71m60, hB_xa71m60, hE_xa71mc0, hB_xa71mc0, hE_xa71mc8, hB_xa71mc8, hE_xa71m100, hB_xa71m100, hE_xa71m160, hB_xa71m160, hE_xa71m168, hB_xa71m168, hE_xa71m170, hB_xa71m170, hE_xa71m178, hB_xa71m178, hE_xa71m180, hB_xa71m180, hE_xa71m188, hB_xa71m188, hE_xa71m190, hB_xa71m190, hE_xa71m198, hB_xa71m198, hE_xa71m1a0, hB_xa71m1a0, hE_xa71m1a8, hB_xa71m1a8, hE_xa71m1b0, hB_xa71m1b0, hE_xa71m1b8, hB_xa71m1b8, hE_xa71m1c0, hB_xa71m1c0, hE_xa71m1c8, hB_xa71m1c8, hE_xa71m218, hB_xa71m218, hE_xa71m220, hB_xa71m220⟩ := hL
  janus64_run [Util.readLE_32, hE_xa71rax, hE_xa71rcx, hE_xa71rdx, hE_xa71rbx, hE_xa71rsi, hE_xa71rdi, hE_xa71r9, hE_xa71r10, hE_xa71r11, hE_xa71r15, hE_xa71m40, hE_xa71m48, hE_xa71m50, hE_xa71m60, hE_xa71mc0, hE_xa71mc8, hE_xa71m100, hE_xa71m160, hE_xa71m168, hE_xa71m170, hE_xa71m178, hE_xa71m180, hE_xa71m188, hE_xa71m190, hE_xa71m198, hE_xa71m1a0, hE_xa71m1a8, hE_xa71m1b0, hE_xa71m1b8, hE_xa71m1c0, hE_xa71m1c8, hE_xa71m218, hE_xa71m220, hsp4, Nat.mod_eq_of_lt hB_xa71rax, Nat.mod_eq_of_lt hB_xa71rcx, Nat.mod_eq_of_lt hB_xa71rdx, Nat.mod_eq_of_lt hB_xa71rbx, Nat.mod_eq_of_lt hB_xa71rsi, Nat.mod_eq_of_lt hB_xa71rdi, Nat.mod_eq_of_lt hB_xa71r9, Nat.mod_eq_of_lt hB_xa71r10, Nat.mod_eq_of_lt hB_xa71r11, Nat.mod_eq_of_lt hB_xa71r15, Nat.mod_eq_of_lt hB_xa71m40, Nat.mod_eq_of_lt hB_xa71m48, Nat.mod_eq_of_lt hB_xa71m50, Nat.mod_eq_of_lt hB_xa71m60, Nat.mod_eq_of_lt hB_xa71mc0, Nat.mod_eq_of_lt hB_xa71mc8, Nat.mod_eq_of_lt hB_xa71m100, Nat.mod_eq_of_lt hB_xa71m160, Nat.mod_eq_of_lt hB_xa71m168, Nat.mod_eq_of_lt hB_xa71m170, Nat.mod_eq_of_lt hB_xa71m178, Nat.mod_eq_of_lt hB_xa71m180, Nat.mod_eq_of_lt hB_xa71m188, Nat.mod_eq_of_lt hB_xa71m190, Nat.mod_eq_of_lt hB_xa71m198, Nat.mod_eq_of_lt hB_xa71m1a0, Nat.mod_eq_of_lt hB_xa71m1a8, Nat.mod_eq_of_lt hB_xa71m1b0, Nat.mod_eq_of_lt hB_xa71m1b8, Nat.mod_eq_of_lt hB_xa71m1c0, Nat.mod_eq_of_lt hB_xa71m1c8, Nat.mod_eq_of_lt hB_xa71m218, Nat.mod_eq_of_lt hB_xa71m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_a71_ab4
  refine ⟨(xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) % 18446744073709551616, (xa71m1a8 + xa71r15 + (xa71m1b8 + xa71r10 + (xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa71m1b8 + xa71r10 + (xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xa71m1c0 + xa71r9) % 18446744073709551616, (xa71mc8 + (xa71m1a8 + xa71r15 + (xa71m1b8 + xa71r10 + (xa71m1b0 + xa71r11 + (xa71m1c8 + xa71rdi + (xa71m1c0 + xa71r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Lab4
    and_intros
    · first | exact hE_xa71rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa71rax)
    · exact hB_xa71rax
    · first | exact hE_xa71rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa71rcx)
    · exact hB_xa71rcx
    · first | exact hE_xa71rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa71rdx)
    · exact hB_xa71rdx
    · first | exact hE_xa71rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa71rbx)
    · exact hB_xa71rbx
    · first | exact hE_xa71rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xa71rsi)
    · exact hB_xa71rsi
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
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m40
    · exact hB_xa71m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m48
    · exact hB_xa71m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m50
    · exact hB_xa71m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m60
    · exact hB_xa71m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71mc0
    · exact hB_xa71mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m100
    · exact hB_xa71m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m160
    · exact hB_xa71m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m168
    · exact hB_xa71m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m170
    · exact hB_xa71m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m178
    · exact hB_xa71m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m180
    · exact hB_xa71m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m188
    · exact hB_xa71m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m190
    · exact hB_xa71m190
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m198
    · exact hB_xa71m198
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m1a0
    · exact hB_xa71m1a0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m218
    · exact hB_xa71m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xa71m220
    · exact hB_xa71m220
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
