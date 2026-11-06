import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_ae4_b27 (s : State) (y3 : Nat) (xae4rax xae4rcx xae4rdx xae4rbx xae4rsi xae4rdi xae4r9 xae4r11 xae4r12 xae4r13 xae4r15 xae4m40 xae4m48 xae4m50 xae4m60 xae4mc0 xae4m100 xae4m160 xae4m168 xae4m170 xae4m178 xae4m180 xae4m188 xae4m220 : Nat) (S' : State) : Prop :=
  ∃ xb27rdi xb27r9 xb27r10 xb27r11 xb27r13 xb27r15, Lb27 s S' xae4rax xae4rcx xae4rdx xae4rbx xae4rsi xb27rdi xb27r9 xb27r10 xb27r11 xae4r12 xb27r13 xb27r15 xae4m40 xae4m48 xae4m50 xae4m60 xae4m100 xae4m160 xae4m168 ∧ xb27rdi = (xae4m220 + xae4r11 + (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xb27r9 = (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xb27r10 = (xae4m180 + xae4r15) % 18446744073709551616 ∧ xb27r11 = (xae4m170 + xae4r13 + (xae4m220 + xae4r11 + (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xb27r13 = (xae4mc0 + (xae4m170 + xae4r13 + (xae4m220 + xae4r11 + (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xb27r15 = (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_ae4_b27 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xae4)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xae4rax xae4rcx xae4rdx xae4rbx xae4rsi xae4rdi xae4r9 xae4r11 xae4r12 xae4r13 xae4r15 xae4m40 xae4m48 xae4m50 xae4m60 xae4mc0 xae4m100 xae4m160 xae4m168 xae4m170 xae4m178 xae4m180 xae4m188 xae4m220 : Nat) (hL : Lae4 s S xae4rax xae4rcx xae4rdx xae4rbx xae4rsi xae4rdi xae4r9 xae4r11 xae4r12 xae4r13 xae4r15 xae4m40 xae4m48 xae4m50 xae4m60 xae4mc0 xae4m100 xae4m160 xae4m168 xae4m170 xae4m178 xae4m180 xae4m188 xae4m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xb27)) S (P_ae4_b27 s y3 xae4rax xae4rcx xae4rdx xae4rbx xae4rsi xae4rdi xae4r9 xae4r11 xae4r12 xae4r13 xae4r15 xae4m40 xae4m48 xae4m50 xae4m60 xae4mc0 xae4m100 xae4m160 xae4m168 xae4m170 xae4m178 xae4m180 xae4m188 xae4m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xae4rax, hB_xae4rax, hE_xae4rcx, hB_xae4rcx, hE_xae4rdx, hB_xae4rdx, hE_xae4rbx, hB_xae4rbx, hE_xae4rsi, hB_xae4rsi, hE_xae4rdi, hB_xae4rdi, hE_xae4r9, hB_xae4r9, hE_xae4r11, hB_xae4r11, hE_xae4r12, hB_xae4r12, hE_xae4r13, hB_xae4r13, hE_xae4r15, hB_xae4r15, hE_xae4m40, hB_xae4m40, hE_xae4m48, hB_xae4m48, hE_xae4m50, hB_xae4m50, hE_xae4m60, hB_xae4m60, hE_xae4mc0, hB_xae4mc0, hE_xae4m100, hB_xae4m100, hE_xae4m160, hB_xae4m160, hE_xae4m168, hB_xae4m168, hE_xae4m170, hB_xae4m170, hE_xae4m178, hB_xae4m178, hE_xae4m180, hB_xae4m180, hE_xae4m188, hB_xae4m188, hE_xae4m220, hB_xae4m220⟩ := hL
  janus64_run [Util.readLE_32, hE_xae4rax, hE_xae4rcx, hE_xae4rdx, hE_xae4rbx, hE_xae4rsi, hE_xae4rdi, hE_xae4r9, hE_xae4r11, hE_xae4r12, hE_xae4r13, hE_xae4r15, hE_xae4m40, hE_xae4m48, hE_xae4m50, hE_xae4m60, hE_xae4mc0, hE_xae4m100, hE_xae4m160, hE_xae4m168, hE_xae4m170, hE_xae4m178, hE_xae4m180, hE_xae4m188, hE_xae4m220, hsp4, Nat.mod_eq_of_lt hB_xae4rax, Nat.mod_eq_of_lt hB_xae4rcx, Nat.mod_eq_of_lt hB_xae4rdx, Nat.mod_eq_of_lt hB_xae4rbx, Nat.mod_eq_of_lt hB_xae4rsi, Nat.mod_eq_of_lt hB_xae4rdi, Nat.mod_eq_of_lt hB_xae4r9, Nat.mod_eq_of_lt hB_xae4r11, Nat.mod_eq_of_lt hB_xae4r12, Nat.mod_eq_of_lt hB_xae4r13, Nat.mod_eq_of_lt hB_xae4r15, Nat.mod_eq_of_lt hB_xae4m40, Nat.mod_eq_of_lt hB_xae4m48, Nat.mod_eq_of_lt hB_xae4m50, Nat.mod_eq_of_lt hB_xae4m60, Nat.mod_eq_of_lt hB_xae4mc0, Nat.mod_eq_of_lt hB_xae4m100, Nat.mod_eq_of_lt hB_xae4m160, Nat.mod_eq_of_lt hB_xae4m168, Nat.mod_eq_of_lt hB_xae4m170, Nat.mod_eq_of_lt hB_xae4m178, Nat.mod_eq_of_lt hB_xae4m180, Nat.mod_eq_of_lt hB_xae4m188, Nat.mod_eq_of_lt hB_xae4m220]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_ae4_b27
  refine ⟨(xae4m220 + xae4r11 + (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xae4m180 + xae4r15) % 18446744073709551616, (xae4m170 + xae4r13 + (xae4m220 + xae4r11 + (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xae4mc0 + (xae4m170 + xae4r13 + (xae4m220 + xae4r11 + (xae4m178 + xae4rdi + (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xae4m188 + xae4r9 + (xae4m180 + xae4r15) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Lb27
    and_intros
    · first | exact hE_xae4rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xae4rax)
    · exact hB_xae4rax
    · first | exact hE_xae4rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xae4rcx)
    · exact hB_xae4rcx
    · first | exact hE_xae4rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xae4rdx)
    · exact hB_xae4rdx
    · first | exact hE_xae4rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xae4rbx)
    · exact hB_xae4rbx
    · first | exact hE_xae4rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xae4rsi)
    · exact hB_xae4rsi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_xae4r12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xae4r12)
    · exact hB_xae4r12
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xae4m40
    · exact hB_xae4m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xae4m48
    · exact hB_xae4m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xae4m50
    · exact hB_xae4m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xae4m60
    · exact hB_xae4m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xae4m100
    · exact hB_xae4m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xae4m160
    · exact hB_xae4m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xae4m168
    · exact hB_xae4m168
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
