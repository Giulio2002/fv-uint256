import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_ab4_ae4 (s : State) (y3 : Nat) (xab4rax xab4rcx xab4rdx xab4rbx xab4rsi xab4rdi xab4r9 xab4r10 xab4r11 xab4r12 xab4r13 xab4m40 xab4m48 xab4m50 xab4m60 xab4mc0 xab4m100 xab4m160 xab4m168 xab4m170 xab4m178 xab4m180 xab4m188 xab4m190 xab4m198 xab4m1a0 xab4m218 xab4m220 : Nat) (S' : State) : Prop :=
  ∃ xae4rdi xae4r9 xae4r11 xae4r13 xae4r15, Lae4 s S' xab4rax xab4rcx xab4rdx xab4rbx xab4rsi xae4rdi xae4r9 xae4r11 xab4r12 xae4r13 xae4r15 xab4m40 xab4m48 xab4m50 xab4m60 xab4mc0 xab4m100 xab4m160 xab4m168 xab4m170 xab4m178 xab4m180 xab4m188 xab4m220 ∧ xae4rdi = (xab4m190 + xab4r11 + (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xae4r9 = (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) % 18446744073709551616 ∧ xae4r11 = (xab4m218 + xab4r10 + (xab4m190 + xab4r11 + (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xae4r13 = (xab4r13 + (xab4m218 + xab4r10 + (xab4m190 + xab4r11 + (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xae4r15 = (xab4m198 + xab4r9) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_ab4_ae4 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xab4)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xab4rax xab4rcx xab4rdx xab4rbx xab4rsi xab4rdi xab4r9 xab4r10 xab4r11 xab4r12 xab4r13 xab4m40 xab4m48 xab4m50 xab4m60 xab4mc0 xab4m100 xab4m160 xab4m168 xab4m170 xab4m178 xab4m180 xab4m188 xab4m190 xab4m198 xab4m1a0 xab4m218 xab4m220 : Nat) (hL : Lab4 s S xab4rax xab4rcx xab4rdx xab4rbx xab4rsi xab4rdi xab4r9 xab4r10 xab4r11 xab4r12 xab4r13 xab4m40 xab4m48 xab4m50 xab4m60 xab4mc0 xab4m100 xab4m160 xab4m168 xab4m170 xab4m178 xab4m180 xab4m188 xab4m190 xab4m198 xab4m1a0 xab4m218 xab4m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xae4)) S (P_ab4_ae4 s y3 xab4rax xab4rcx xab4rdx xab4rbx xab4rsi xab4rdi xab4r9 xab4r10 xab4r11 xab4r12 xab4r13 xab4m40 xab4m48 xab4m50 xab4m60 xab4mc0 xab4m100 xab4m160 xab4m168 xab4m170 xab4m178 xab4m180 xab4m188 xab4m190 xab4m198 xab4m1a0 xab4m218 xab4m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xab4rax, hB_xab4rax, hE_xab4rcx, hB_xab4rcx, hE_xab4rdx, hB_xab4rdx, hE_xab4rbx, hB_xab4rbx, hE_xab4rsi, hB_xab4rsi, hE_xab4rdi, hB_xab4rdi, hE_xab4r9, hB_xab4r9, hE_xab4r10, hB_xab4r10, hE_xab4r11, hB_xab4r11, hE_xab4r12, hB_xab4r12, hE_xab4r13, hB_xab4r13, hE_xab4m40, hB_xab4m40, hE_xab4m48, hB_xab4m48, hE_xab4m50, hB_xab4m50, hE_xab4m60, hB_xab4m60, hE_xab4mc0, hB_xab4mc0, hE_xab4m100, hB_xab4m100, hE_xab4m160, hB_xab4m160, hE_xab4m168, hB_xab4m168, hE_xab4m170, hB_xab4m170, hE_xab4m178, hB_xab4m178, hE_xab4m180, hB_xab4m180, hE_xab4m188, hB_xab4m188, hE_xab4m190, hB_xab4m190, hE_xab4m198, hB_xab4m198, hE_xab4m1a0, hB_xab4m1a0, hE_xab4m218, hB_xab4m218, hE_xab4m220, hB_xab4m220⟩ := hL
  janus64_run [Util.readLE_32, hE_xab4rax, hE_xab4rcx, hE_xab4rdx, hE_xab4rbx, hE_xab4rsi, hE_xab4rdi, hE_xab4r9, hE_xab4r10, hE_xab4r11, hE_xab4r12, hE_xab4r13, hE_xab4m40, hE_xab4m48, hE_xab4m50, hE_xab4m60, hE_xab4mc0, hE_xab4m100, hE_xab4m160, hE_xab4m168, hE_xab4m170, hE_xab4m178, hE_xab4m180, hE_xab4m188, hE_xab4m190, hE_xab4m198, hE_xab4m1a0, hE_xab4m218, hE_xab4m220, hsp4, Nat.mod_eq_of_lt hB_xab4rax, Nat.mod_eq_of_lt hB_xab4rcx, Nat.mod_eq_of_lt hB_xab4rdx, Nat.mod_eq_of_lt hB_xab4rbx, Nat.mod_eq_of_lt hB_xab4rsi, Nat.mod_eq_of_lt hB_xab4rdi, Nat.mod_eq_of_lt hB_xab4r9, Nat.mod_eq_of_lt hB_xab4r10, Nat.mod_eq_of_lt hB_xab4r11, Nat.mod_eq_of_lt hB_xab4r12, Nat.mod_eq_of_lt hB_xab4r13, Nat.mod_eq_of_lt hB_xab4m40, Nat.mod_eq_of_lt hB_xab4m48, Nat.mod_eq_of_lt hB_xab4m50, Nat.mod_eq_of_lt hB_xab4m60, Nat.mod_eq_of_lt hB_xab4mc0, Nat.mod_eq_of_lt hB_xab4m100, Nat.mod_eq_of_lt hB_xab4m160, Nat.mod_eq_of_lt hB_xab4m168, Nat.mod_eq_of_lt hB_xab4m170, Nat.mod_eq_of_lt hB_xab4m178, Nat.mod_eq_of_lt hB_xab4m180, Nat.mod_eq_of_lt hB_xab4m188, Nat.mod_eq_of_lt hB_xab4m190, Nat.mod_eq_of_lt hB_xab4m198, Nat.mod_eq_of_lt hB_xab4m1a0, Nat.mod_eq_of_lt hB_xab4m218, Nat.mod_eq_of_lt hB_xab4m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_ab4_ae4
  refine ⟨(xab4m190 + xab4r11 + (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) % 18446744073709551616, (xab4m218 + xab4r10 + (xab4m190 + xab4r11 + (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xab4r13 + (xab4m218 + xab4r10 + (xab4m190 + xab4r11 + (xab4m1a0 + xab4rdi + (xab4m198 + xab4r9) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xab4m198 + xab4r9) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Lae4
    and_intros
    · first | exact hE_xab4rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xab4rax)
    · exact hB_xab4rax
    · first | exact hE_xab4rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xab4rcx)
    · exact hB_xab4rcx
    · first | exact hE_xab4rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xab4rdx)
    · exact hB_xab4rdx
    · first | exact hE_xab4rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xab4rbx)
    · exact hB_xab4rbx
    · first | exact hE_xab4rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xab4rsi)
    · exact hB_xab4rsi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_xab4r12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xab4r12)
    · exact hB_xab4r12
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m40
    · exact hB_xab4m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m48
    · exact hB_xab4m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m50
    · exact hB_xab4m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m60
    · exact hB_xab4m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4mc0
    · exact hB_xab4mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m100
    · exact hB_xab4m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m160
    · exact hB_xab4m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m168
    · exact hB_xab4m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m170
    · exact hB_xab4m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m178
    · exact hB_xab4m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m180
    · exact hB_xab4m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m188
    · exact hB_xab4m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xab4m220
    · exact hB_xab4m220
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
