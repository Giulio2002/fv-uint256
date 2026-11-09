import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_660_689 (s : State) (y3 : Nat) (x660rax x660rcx x660rdi x660r8 x660r9 x660r10 x660r15 x660m38 x660m40 x660m48 x660m50 x660m58 x660m68 x660m70 x660m98 x660ma0 x660ma8 x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x660m198 x660m1a0 x660m1a8 x660m1b0 x660m1b8 x660m1c0 x660m1c8 x660m1d0 x660m1d8 x660m1e0 x660m1e8 x660m1f0 x660m1f8 x660m200 x660m208 x660m210 x660m218 x660m220 : Nat) (S' : State) : Prop :=
  ∃ x689rdx x689rsi x689r13, L689 s S' x660rax x660rcx x689rdx x689rsi x660rdi x660r8 x660r9 x660r10 x689r13 x660r15 x660m38 x660m40 x660m68 x660m70 x660m98 x660ma0 x660ma8 x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x660m198 x660m1a0 x660m1a8 x660m1b0 x660m1b8 x660m1c0 x660m1c8 x660m1d0 x660m1d8 x660m1e0 x660m1e8 x660m1f0 x660m208 x660m210 x660m218 x660m220 ∧ x689rdx = (x660m48 + (x660m200 + x660m50 + (x660m1f8 + x660m58) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x689rsi = (x660m1f8 + x660m58) % 18446744073709551616 ∧ x689r13 = (x660m200 + x660m50 + (x660m1f8 + x660m58) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_660_689 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x660)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x660rax x660rcx x660rdi x660r8 x660r9 x660r10 x660r15 x660m38 x660m40 x660m48 x660m50 x660m58 x660m68 x660m70 x660m98 x660ma0 x660ma8 x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x660m198 x660m1a0 x660m1a8 x660m1b0 x660m1b8 x660m1c0 x660m1c8 x660m1d0 x660m1d8 x660m1e0 x660m1e8 x660m1f0 x660m1f8 x660m200 x660m208 x660m210 x660m218 x660m220 : Nat) (hL : L660 s S x660rax x660rcx x660rdi x660r8 x660r9 x660r10 x660r15 x660m38 x660m40 x660m48 x660m50 x660m58 x660m68 x660m70 x660m98 x660ma0 x660ma8 x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x660m198 x660m1a0 x660m1a8 x660m1b0 x660m1b8 x660m1c0 x660m1c8 x660m1d0 x660m1d8 x660m1e0 x660m1e8 x660m1f0 x660m1f8 x660m200 x660m208 x660m210 x660m218 x660m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x689)) S (P_660_689 s y3 x660rax x660rcx x660rdi x660r8 x660r9 x660r10 x660r15 x660m38 x660m40 x660m48 x660m50 x660m58 x660m68 x660m70 x660m98 x660ma0 x660ma8 x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x660m198 x660m1a0 x660m1a8 x660m1b0 x660m1b8 x660m1c0 x660m1c8 x660m1d0 x660m1d8 x660m1e0 x660m1e8 x660m1f0 x660m1f8 x660m200 x660m208 x660m210 x660m218 x660m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x660rax, hB_x660rax, hE_x660rcx, hB_x660rcx, hE_x660rdi, hB_x660rdi, hE_x660r8, hB_x660r8, hE_x660r9, hB_x660r9, hE_x660r10, hB_x660r10, hE_x660r15, hB_x660r15, hE_x660m38, hB_x660m38, hE_x660m40, hB_x660m40, hE_x660m48, hB_x660m48, hE_x660m50, hB_x660m50, hE_x660m58, hB_x660m58, hE_x660m68, hB_x660m68, hE_x660m70, hB_x660m70, hE_x660m98, hB_x660m98, hE_x660ma0, hB_x660ma0, hE_x660ma8, hB_x660ma8, hE_x660m150, hB_x660m150, hE_x660m158, hB_x660m158, hE_x660m160, hB_x660m160, hE_x660m168, hB_x660m168, hE_x660m170, hB_x660m170, hE_x660m178, hB_x660m178, hE_x660m180, hB_x660m180, hE_x660m188, hB_x660m188, hE_x660m190, hB_x660m190, hE_x660m198, hB_x660m198, hE_x660m1a0, hB_x660m1a0, hE_x660m1a8, hB_x660m1a8, hE_x660m1b0, hB_x660m1b0, hE_x660m1b8, hB_x660m1b8, hE_x660m1c0, hB_x660m1c0, hE_x660m1c8, hB_x660m1c8, hE_x660m1d0, hB_x660m1d0, hE_x660m1d8, hB_x660m1d8, hE_x660m1e0, hB_x660m1e0, hE_x660m1e8, hB_x660m1e8, hE_x660m1f0, hB_x660m1f0, hE_x660m1f8, hB_x660m1f8, hE_x660m200, hB_x660m200, hE_x660m208, hB_x660m208, hE_x660m210, hB_x660m210, hE_x660m218, hB_x660m218, hE_x660m220, hB_x660m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x660rax, hE_x660rcx, hE_x660rdi, hE_x660r8, hE_x660r9, hE_x660r10, hE_x660r15, hE_x660m38, hE_x660m40, hE_x660m48, hE_x660m50, hE_x660m58, hE_x660m68, hE_x660m70, hE_x660m98, hE_x660ma0, hE_x660ma8, hE_x660m150, hE_x660m158, hE_x660m160, hE_x660m168, hE_x660m170, hE_x660m178, hE_x660m180, hE_x660m188, hE_x660m190, hE_x660m198, hE_x660m1a0, hE_x660m1a8, hE_x660m1b0, hE_x660m1b8, hE_x660m1c0, hE_x660m1c8, hE_x660m1d0, hE_x660m1d8, hE_x660m1e0, hE_x660m1e8, hE_x660m1f0, hE_x660m1f8, hE_x660m200, hE_x660m208, hE_x660m210, hE_x660m218, hE_x660m220, hsp4, Nat.mod_eq_of_lt hB_x660rax, Nat.mod_eq_of_lt hB_x660rcx, Nat.mod_eq_of_lt hB_x660rdi, Nat.mod_eq_of_lt hB_x660r8, Nat.mod_eq_of_lt hB_x660r9, Nat.mod_eq_of_lt hB_x660r10, Nat.mod_eq_of_lt hB_x660r15, Nat.mod_eq_of_lt hB_x660m38, Nat.mod_eq_of_lt hB_x660m40, Nat.mod_eq_of_lt hB_x660m48, Nat.mod_eq_of_lt hB_x660m50, Nat.mod_eq_of_lt hB_x660m58, Nat.mod_eq_of_lt hB_x660m68, Nat.mod_eq_of_lt hB_x660m70, Nat.mod_eq_of_lt hB_x660m98, Nat.mod_eq_of_lt hB_x660ma0, Nat.mod_eq_of_lt hB_x660ma8, Nat.mod_eq_of_lt hB_x660m150, Nat.mod_eq_of_lt hB_x660m158, Nat.mod_eq_of_lt hB_x660m160, Nat.mod_eq_of_lt hB_x660m168, Nat.mod_eq_of_lt hB_x660m170, Nat.mod_eq_of_lt hB_x660m178, Nat.mod_eq_of_lt hB_x660m180, Nat.mod_eq_of_lt hB_x660m188, Nat.mod_eq_of_lt hB_x660m190, Nat.mod_eq_of_lt hB_x660m198, Nat.mod_eq_of_lt hB_x660m1a0, Nat.mod_eq_of_lt hB_x660m1a8, Nat.mod_eq_of_lt hB_x660m1b0, Nat.mod_eq_of_lt hB_x660m1b8, Nat.mod_eq_of_lt hB_x660m1c0, Nat.mod_eq_of_lt hB_x660m1c8, Nat.mod_eq_of_lt hB_x660m1d0, Nat.mod_eq_of_lt hB_x660m1d8, Nat.mod_eq_of_lt hB_x660m1e0, Nat.mod_eq_of_lt hB_x660m1e8, Nat.mod_eq_of_lt hB_x660m1f0, Nat.mod_eq_of_lt hB_x660m1f8, Nat.mod_eq_of_lt hB_x660m200, Nat.mod_eq_of_lt hB_x660m208, Nat.mod_eq_of_lt hB_x660m210, Nat.mod_eq_of_lt hB_x660m218, Nat.mod_eq_of_lt hB_x660m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_660_689
  refine ⟨(x660m48 + (x660m200 + x660m50 + (x660m1f8 + x660m58) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x660m1f8 + x660m58) % 18446744073709551616, (x660m200 + x660m50 + (x660m1f8 + x660m58) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L689
    and_intros
    · first | exact hE_x660rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x660rax)
    · exact hB_x660rax
    · first | exact hE_x660rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x660rcx)
    · exact hB_x660rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x660rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x660rdi)
    · exact hB_x660rdi
    · first | exact hE_x660r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x660r8)
    · exact hB_x660r8
    · first | exact hE_x660r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x660r9)
    · exact hB_x660r9
    · first | exact hE_x660r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x660r10)
    · exact hB_x660r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x660r15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x660r15)
    · exact hB_x660r15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m38
    · exact hB_x660m38
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m40
    · exact hB_x660m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m68
    · exact hB_x660m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m70
    · exact hB_x660m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m98
    · exact hB_x660m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660ma0
    · exact hB_x660ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660ma8
    · exact hB_x660ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m150
    · exact hB_x660m150
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m158
    · exact hB_x660m158
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m160
    · exact hB_x660m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m168
    · exact hB_x660m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m170
    · exact hB_x660m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m178
    · exact hB_x660m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m180
    · exact hB_x660m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m188
    · exact hB_x660m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m190
    · exact hB_x660m190
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m198
    · exact hB_x660m198
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1a0
    · exact hB_x660m1a0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1a8
    · exact hB_x660m1a8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1b0
    · exact hB_x660m1b0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1b8
    · exact hB_x660m1b8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1c0
    · exact hB_x660m1c0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1c8
    · exact hB_x660m1c8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1d0
    · exact hB_x660m1d0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1d8
    · exact hB_x660m1d8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1e0
    · exact hB_x660m1e0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1e8
    · exact hB_x660m1e8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m1f0
    · exact hB_x660m1f0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m208
    · exact hB_x660m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m210
    · exact hB_x660m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m218
    · exact hB_x660m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x660m220
    · exact hB_x660m220
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
