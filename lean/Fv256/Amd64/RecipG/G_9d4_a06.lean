import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_9d4_a06 (s : State) (y3 : Nat) (x9d4rax x9d4rcx x9d4rdx x9d4rbx x9d4r10 x9d4r11 x9d4r12 x9d4r13 x9d4r15 x9d4m40 x9d4m48 x9d4m50 x9d4m60 x9d4m68 x9d4m70 x9d4mc0 x9d4mc8 x9d4md0 x9d4md8 x9d4me0 x9d4m100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x9d4m1a8 x9d4m1b0 x9d4m1b8 x9d4m1c0 x9d4m1c8 x9d4m1d0 x9d4m1d8 x9d4m1e0 x9d4m1e8 x9d4m1f0 x9d4m1f8 x9d4m200 x9d4m208 x9d4m210 x9d4m218 x9d4m220 : Nat) (S' : State) : Prop :=
  ∃ xa06rdi xa06r10 xa06r12 xa06r13 xa06r15, La06 s S' x9d4rax x9d4rcx x9d4rdx x9d4rbx xa06rdi xa06r10 x9d4r11 xa06r12 xa06r13 xa06r15 x9d4m40 x9d4m48 x9d4m50 x9d4m60 x9d4mc0 x9d4mc8 x9d4md0 x9d4m100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x9d4m1a8 x9d4m1b0 x9d4m1b8 x9d4m1c0 x9d4m1c8 x9d4m1d0 x9d4m1d8 x9d4m1e0 x9d4m1e8 x9d4m1f0 x9d4m1f8 x9d4m200 x9d4m210 x9d4m218 x9d4m220 ∧ xa06rdi = (x9d4m70 + x9d4r12) % 18446744073709551616 ∧ xa06r10 = (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) % 18446744073709551616 ∧ xa06r12 = (x9d4m208 + x9d4r15 + (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xa06r13 = (x9d4m68 + x9d4me0 + (x9d4m208 + x9d4r15 + (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ xa06r15 = (x9d4md8 + (x9d4m68 + x9d4me0 + (x9d4m208 + x9d4r15 + (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_9d4_a06 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x9d4)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x9d4rax x9d4rcx x9d4rdx x9d4rbx x9d4r10 x9d4r11 x9d4r12 x9d4r13 x9d4r15 x9d4m40 x9d4m48 x9d4m50 x9d4m60 x9d4m68 x9d4m70 x9d4mc0 x9d4mc8 x9d4md0 x9d4md8 x9d4me0 x9d4m100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x9d4m1a8 x9d4m1b0 x9d4m1b8 x9d4m1c0 x9d4m1c8 x9d4m1d0 x9d4m1d8 x9d4m1e0 x9d4m1e8 x9d4m1f0 x9d4m1f8 x9d4m200 x9d4m208 x9d4m210 x9d4m218 x9d4m220 : Nat) (hL : L9d4 s S x9d4rax x9d4rcx x9d4rdx x9d4rbx x9d4r10 x9d4r11 x9d4r12 x9d4r13 x9d4r15 x9d4m40 x9d4m48 x9d4m50 x9d4m60 x9d4m68 x9d4m70 x9d4mc0 x9d4mc8 x9d4md0 x9d4md8 x9d4me0 x9d4m100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x9d4m1a8 x9d4m1b0 x9d4m1b8 x9d4m1c0 x9d4m1c8 x9d4m1d0 x9d4m1d8 x9d4m1e0 x9d4m1e8 x9d4m1f0 x9d4m1f8 x9d4m200 x9d4m208 x9d4m210 x9d4m218 x9d4m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xa06)) S (P_9d4_a06 s y3 x9d4rax x9d4rcx x9d4rdx x9d4rbx x9d4r10 x9d4r11 x9d4r12 x9d4r13 x9d4r15 x9d4m40 x9d4m48 x9d4m50 x9d4m60 x9d4m68 x9d4m70 x9d4mc0 x9d4mc8 x9d4md0 x9d4md8 x9d4me0 x9d4m100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x9d4m1a8 x9d4m1b0 x9d4m1b8 x9d4m1c0 x9d4m1c8 x9d4m1d0 x9d4m1d8 x9d4m1e0 x9d4m1e8 x9d4m1f0 x9d4m1f8 x9d4m200 x9d4m208 x9d4m210 x9d4m218 x9d4m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x9d4rax, hB_x9d4rax, hE_x9d4rcx, hB_x9d4rcx, hE_x9d4rdx, hB_x9d4rdx, hE_x9d4rbx, hB_x9d4rbx, hE_x9d4r10, hB_x9d4r10, hE_x9d4r11, hB_x9d4r11, hE_x9d4r12, hB_x9d4r12, hE_x9d4r13, hB_x9d4r13, hE_x9d4r15, hB_x9d4r15, hE_x9d4m40, hB_x9d4m40, hE_x9d4m48, hB_x9d4m48, hE_x9d4m50, hB_x9d4m50, hE_x9d4m60, hB_x9d4m60, hE_x9d4m68, hB_x9d4m68, hE_x9d4m70, hB_x9d4m70, hE_x9d4mc0, hB_x9d4mc0, hE_x9d4mc8, hB_x9d4mc8, hE_x9d4md0, hB_x9d4md0, hE_x9d4md8, hB_x9d4md8, hE_x9d4me0, hB_x9d4me0, hE_x9d4m100, hB_x9d4m100, hE_x9d4m160, hB_x9d4m160, hE_x9d4m168, hB_x9d4m168, hE_x9d4m170, hB_x9d4m170, hE_x9d4m178, hB_x9d4m178, hE_x9d4m180, hB_x9d4m180, hE_x9d4m188, hB_x9d4m188, hE_x9d4m190, hB_x9d4m190, hE_x9d4m198, hB_x9d4m198, hE_x9d4m1a0, hB_x9d4m1a0, hE_x9d4m1a8, hB_x9d4m1a8, hE_x9d4m1b0, hB_x9d4m1b0, hE_x9d4m1b8, hB_x9d4m1b8, hE_x9d4m1c0, hB_x9d4m1c0, hE_x9d4m1c8, hB_x9d4m1c8, hE_x9d4m1d0, hB_x9d4m1d0, hE_x9d4m1d8, hB_x9d4m1d8, hE_x9d4m1e0, hB_x9d4m1e0, hE_x9d4m1e8, hB_x9d4m1e8, hE_x9d4m1f0, hB_x9d4m1f0, hE_x9d4m1f8, hB_x9d4m1f8, hE_x9d4m200, hB_x9d4m200, hE_x9d4m208, hB_x9d4m208, hE_x9d4m210, hB_x9d4m210, hE_x9d4m218, hB_x9d4m218, hE_x9d4m220, hB_x9d4m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x9d4rax, hE_x9d4rcx, hE_x9d4rdx, hE_x9d4rbx, hE_x9d4r10, hE_x9d4r11, hE_x9d4r12, hE_x9d4r13, hE_x9d4r15, hE_x9d4m40, hE_x9d4m48, hE_x9d4m50, hE_x9d4m60, hE_x9d4m68, hE_x9d4m70, hE_x9d4mc0, hE_x9d4mc8, hE_x9d4md0, hE_x9d4md8, hE_x9d4me0, hE_x9d4m100, hE_x9d4m160, hE_x9d4m168, hE_x9d4m170, hE_x9d4m178, hE_x9d4m180, hE_x9d4m188, hE_x9d4m190, hE_x9d4m198, hE_x9d4m1a0, hE_x9d4m1a8, hE_x9d4m1b0, hE_x9d4m1b8, hE_x9d4m1c0, hE_x9d4m1c8, hE_x9d4m1d0, hE_x9d4m1d8, hE_x9d4m1e0, hE_x9d4m1e8, hE_x9d4m1f0, hE_x9d4m1f8, hE_x9d4m200, hE_x9d4m208, hE_x9d4m210, hE_x9d4m218, hE_x9d4m220, hsp4, Nat.mod_eq_of_lt hB_x9d4rax, Nat.mod_eq_of_lt hB_x9d4rcx, Nat.mod_eq_of_lt hB_x9d4rdx, Nat.mod_eq_of_lt hB_x9d4rbx, Nat.mod_eq_of_lt hB_x9d4r10, Nat.mod_eq_of_lt hB_x9d4r11, Nat.mod_eq_of_lt hB_x9d4r12, Nat.mod_eq_of_lt hB_x9d4r13, Nat.mod_eq_of_lt hB_x9d4r15, Nat.mod_eq_of_lt hB_x9d4m40, Nat.mod_eq_of_lt hB_x9d4m48, Nat.mod_eq_of_lt hB_x9d4m50, Nat.mod_eq_of_lt hB_x9d4m60, Nat.mod_eq_of_lt hB_x9d4m68, Nat.mod_eq_of_lt hB_x9d4m70, Nat.mod_eq_of_lt hB_x9d4mc0, Nat.mod_eq_of_lt hB_x9d4mc8, Nat.mod_eq_of_lt hB_x9d4md0, Nat.mod_eq_of_lt hB_x9d4md8, Nat.mod_eq_of_lt hB_x9d4me0, Nat.mod_eq_of_lt hB_x9d4m100, Nat.mod_eq_of_lt hB_x9d4m160, Nat.mod_eq_of_lt hB_x9d4m168, Nat.mod_eq_of_lt hB_x9d4m170, Nat.mod_eq_of_lt hB_x9d4m178, Nat.mod_eq_of_lt hB_x9d4m180, Nat.mod_eq_of_lt hB_x9d4m188, Nat.mod_eq_of_lt hB_x9d4m190, Nat.mod_eq_of_lt hB_x9d4m198, Nat.mod_eq_of_lt hB_x9d4m1a0, Nat.mod_eq_of_lt hB_x9d4m1a8, Nat.mod_eq_of_lt hB_x9d4m1b0, Nat.mod_eq_of_lt hB_x9d4m1b8, Nat.mod_eq_of_lt hB_x9d4m1c0, Nat.mod_eq_of_lt hB_x9d4m1c8, Nat.mod_eq_of_lt hB_x9d4m1d0, Nat.mod_eq_of_lt hB_x9d4m1d8, Nat.mod_eq_of_lt hB_x9d4m1e0, Nat.mod_eq_of_lt hB_x9d4m1e8, Nat.mod_eq_of_lt hB_x9d4m1f0, Nat.mod_eq_of_lt hB_x9d4m1f8, Nat.mod_eq_of_lt hB_x9d4m200, Nat.mod_eq_of_lt hB_x9d4m208, Nat.mod_eq_of_lt hB_x9d4m210, Nat.mod_eq_of_lt hB_x9d4m218, Nat.mod_eq_of_lt hB_x9d4m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_9d4_a06
  refine ⟨(x9d4m70 + x9d4r12) % 18446744073709551616, (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) % 18446744073709551616, (x9d4m208 + x9d4r15 + (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x9d4m68 + x9d4me0 + (x9d4m208 + x9d4r15 + (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x9d4md8 + (x9d4m68 + x9d4me0 + (x9d4m208 + x9d4r15 + (x9d4r10 + x9d4r13 + (x9d4m70 + x9d4r12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold La06
    and_intros
    · first | exact hE_x9d4rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x9d4rax)
    · exact hB_x9d4rax
    · first | exact hE_x9d4rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x9d4rcx)
    · exact hB_x9d4rcx
    · first | exact hE_x9d4rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x9d4rdx)
    · exact hB_x9d4rdx
    · first | exact hE_x9d4rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x9d4rbx)
    · exact hB_x9d4rbx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x9d4r11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x9d4r11)
    · exact hB_x9d4r11
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m40
    · exact hB_x9d4m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m48
    · exact hB_x9d4m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m50
    · exact hB_x9d4m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m60
    · exact hB_x9d4m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4mc0
    · exact hB_x9d4mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4mc8
    · exact hB_x9d4mc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4md0
    · exact hB_x9d4md0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m100
    · exact hB_x9d4m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m160
    · exact hB_x9d4m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m168
    · exact hB_x9d4m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m170
    · exact hB_x9d4m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m178
    · exact hB_x9d4m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m180
    · exact hB_x9d4m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m188
    · exact hB_x9d4m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m190
    · exact hB_x9d4m190
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m198
    · exact hB_x9d4m198
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1a0
    · exact hB_x9d4m1a0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1a8
    · exact hB_x9d4m1a8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1b0
    · exact hB_x9d4m1b0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1b8
    · exact hB_x9d4m1b8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1c0
    · exact hB_x9d4m1c0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1c8
    · exact hB_x9d4m1c8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1d0
    · exact hB_x9d4m1d0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1d8
    · exact hB_x9d4m1d8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1e0
    · exact hB_x9d4m1e0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1e8
    · exact hB_x9d4m1e8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1f0
    · exact hB_x9d4m1f0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m1f8
    · exact hB_x9d4m1f8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m200
    · exact hB_x9d4m200
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m210
    · exact hB_x9d4m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m218
    · exact hB_x9d4m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x9d4m220
    · exact hB_x9d4m220
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
