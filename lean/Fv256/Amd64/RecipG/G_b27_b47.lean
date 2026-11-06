import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_b27_b47 (s : State) (y3 : Nat) (xb27rax xb27rcx xb27rdx xb27rbx xb27rsi xb27rdi xb27r9 xb27r10 xb27r11 xb27r12 xb27r13 xb27r15 xb27m40 xb27m48 xb27m50 xb27m60 xb27m100 xb27m160 xb27m168 : Nat) (S' : State) : Prop :=
  ∃ xb47rax xb47rdx xb47r8 xb47r13 xb47r15, Lb47 s S' xb47rax xb27rcx xb47rdx xb27rbx xb27rsi xb47r8 xb27r10 xb27r12 xb47r13 xb47r15 xb27m40 xb27m48 xb27m50 xb27m60 xb27m100 ∧ xb47rax = (xb27rax + xb27rdi + (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xb47rdx = (xb27rdx + xb27r11 + (xb27rax + xb27rdi + (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xb47r8 = (xb27m160 + xb27r15) % 18446744073709551616 ∧ xb47r13 = (xb27r13 + (xb27rdx + xb27r11 + (xb27rax + xb27rdi + (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xb47r15 = (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_b27_b47 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xb27)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xb27rax xb27rcx xb27rdx xb27rbx xb27rsi xb27rdi xb27r9 xb27r10 xb27r11 xb27r12 xb27r13 xb27r15 xb27m40 xb27m48 xb27m50 xb27m60 xb27m100 xb27m160 xb27m168 : Nat) (hL : Lb27 s S xb27rax xb27rcx xb27rdx xb27rbx xb27rsi xb27rdi xb27r9 xb27r10 xb27r11 xb27r12 xb27r13 xb27r15 xb27m40 xb27m48 xb27m50 xb27m60 xb27m100 xb27m160 xb27m168) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xb47)) S (P_b27_b47 s y3 xb27rax xb27rcx xb27rdx xb27rbx xb27rsi xb27rdi xb27r9 xb27r10 xb27r11 xb27r12 xb27r13 xb27r15 xb27m40 xb27m48 xb27m50 xb27m60 xb27m100 xb27m160 xb27m168) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xb27rax, hB_xb27rax, hE_xb27rcx, hB_xb27rcx, hE_xb27rdx, hB_xb27rdx, hE_xb27rbx, hB_xb27rbx, hE_xb27rsi, hB_xb27rsi, hE_xb27rdi, hB_xb27rdi, hE_xb27r9, hB_xb27r9, hE_xb27r10, hB_xb27r10, hE_xb27r11, hB_xb27r11, hE_xb27r12, hB_xb27r12, hE_xb27r13, hB_xb27r13, hE_xb27r15, hB_xb27r15, hE_xb27m40, hB_xb27m40, hE_xb27m48, hB_xb27m48, hE_xb27m50, hB_xb27m50, hE_xb27m60, hB_xb27m60, hE_xb27m100, hB_xb27m100, hE_xb27m160, hB_xb27m160, hE_xb27m168, hB_xb27m168⟩ := hL
  janus64_run [Util.readLE_32, hE_xb27rax, hE_xb27rcx, hE_xb27rdx, hE_xb27rbx, hE_xb27rsi, hE_xb27rdi, hE_xb27r9, hE_xb27r10, hE_xb27r11, hE_xb27r12, hE_xb27r13, hE_xb27r15, hE_xb27m40, hE_xb27m48, hE_xb27m50, hE_xb27m60, hE_xb27m100, hE_xb27m160, hE_xb27m168, hsp4, Nat.mod_eq_of_lt hB_xb27rax, Nat.mod_eq_of_lt hB_xb27rcx, Nat.mod_eq_of_lt hB_xb27rdx, Nat.mod_eq_of_lt hB_xb27rbx, Nat.mod_eq_of_lt hB_xb27rsi, Nat.mod_eq_of_lt hB_xb27rdi, Nat.mod_eq_of_lt hB_xb27r9, Nat.mod_eq_of_lt hB_xb27r10, Nat.mod_eq_of_lt hB_xb27r11, Nat.mod_eq_of_lt hB_xb27r12, Nat.mod_eq_of_lt hB_xb27r13, Nat.mod_eq_of_lt hB_xb27r15, Nat.mod_eq_of_lt hB_xb27m40, Nat.mod_eq_of_lt hB_xb27m48, Nat.mod_eq_of_lt hB_xb27m50, Nat.mod_eq_of_lt hB_xb27m60, Nat.mod_eq_of_lt hB_xb27m100, Nat.mod_eq_of_lt hB_xb27m160, Nat.mod_eq_of_lt hB_xb27m168]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_b27_b47
  refine ⟨(xb27rax + xb27rdi + (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xb27rdx + xb27r11 + (xb27rax + xb27rdi + (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xb27m160 + xb27r15) % 18446744073709551616, (xb27r13 + (xb27rdx + xb27r11 + (xb27rax + xb27rdi + (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (xb27m168 + xb27r9 + (xb27m160 + xb27r15) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Lb47
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_xb27rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb27rcx)
    · exact hB_xb27rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_xb27rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb27rbx)
    · exact hB_xb27rbx
    · first | exact hE_xb27rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb27rsi)
    · exact hB_xb27rsi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_xb27r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb27r10)
    · exact hB_xb27r10
    · first | exact hE_xb27r12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb27r12)
    · exact hB_xb27r12
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb27m40
    · exact hB_xb27m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb27m48
    · exact hB_xb27m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb27m50
    · exact hB_xb27m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb27m60
    · exact hB_xb27m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb27m100
    · exact hB_xb27m100
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
