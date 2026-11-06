import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_689_6b3 (s : State) (y3 : Nat) (x689rax x689rcx x689rdx x689rsi x689rdi x689r8 x689r9 x689r10 x689r13 x689r15 x689m38 x689m40 x689m68 x689m70 x689m98 x689ma0 x689ma8 x689m150 x689m158 x689m160 x689m168 x689m170 x689m178 x689m180 x689m188 x689m190 x689m198 x689m1a0 x689m1a8 x689m1b0 x689m1b8 x689m1c0 x689m1c8 x689m1d0 x689m1d8 x689m1e0 x689m1e8 x689m1f0 x689m208 x689m210 x689m218 x689m220 : Nat) (S' : State) : Prop :=
  ∃ x6b3rdx x6b3rbx x6b3rsi x6b3r13, L6b3 s S' x689rax x689rcx x6b3rdx x6b3rbx x6b3rsi x689rdi x689r8 x689r9 x689r10 x6b3r13 x689r15 x689m38 x689m68 x689m70 x689m98 x689ma0 x689ma8 x689m150 x689m158 x689m160 x689m168 x689m170 x689m178 x689m180 x689m188 x689m190 x689m198 x689m1a0 x689m1a8 x689m1b0 x689m1b8 x689m1c0 x689m1c8 x689m1d0 x689m1d8 x689m208 x689m210 x689m218 x689m220 ∧ x6b3rdx = (x689m40 + (x689m1e0 + x689rdx + (x689m1f0 + x689r13 + (x689m1e8 + x689rsi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x6b3rbx = (x689m1e8 + x689rsi) % 18446744073709551616 ∧ x6b3rsi = (x689m1f0 + x689r13 + (x689m1e8 + x689rsi) / 18446744073709551616) % 18446744073709551616 ∧ x6b3r13 = (x689m1e0 + x689rdx + (x689m1f0 + x689r13 + (x689m1e8 + x689rsi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_689_6b3 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x689)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x689rax x689rcx x689rdx x689rsi x689rdi x689r8 x689r9 x689r10 x689r13 x689r15 x689m38 x689m40 x689m68 x689m70 x689m98 x689ma0 x689ma8 x689m150 x689m158 x689m160 x689m168 x689m170 x689m178 x689m180 x689m188 x689m190 x689m198 x689m1a0 x689m1a8 x689m1b0 x689m1b8 x689m1c0 x689m1c8 x689m1d0 x689m1d8 x689m1e0 x689m1e8 x689m1f0 x689m208 x689m210 x689m218 x689m220 : Nat) (hL : L689 s S x689rax x689rcx x689rdx x689rsi x689rdi x689r8 x689r9 x689r10 x689r13 x689r15 x689m38 x689m40 x689m68 x689m70 x689m98 x689ma0 x689ma8 x689m150 x689m158 x689m160 x689m168 x689m170 x689m178 x689m180 x689m188 x689m190 x689m198 x689m1a0 x689m1a8 x689m1b0 x689m1b8 x689m1c0 x689m1c8 x689m1d0 x689m1d8 x689m1e0 x689m1e8 x689m1f0 x689m208 x689m210 x689m218 x689m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x6b3)) S (P_689_6b3 s y3 x689rax x689rcx x689rdx x689rsi x689rdi x689r8 x689r9 x689r10 x689r13 x689r15 x689m38 x689m40 x689m68 x689m70 x689m98 x689ma0 x689ma8 x689m150 x689m158 x689m160 x689m168 x689m170 x689m178 x689m180 x689m188 x689m190 x689m198 x689m1a0 x689m1a8 x689m1b0 x689m1b8 x689m1c0 x689m1c8 x689m1d0 x689m1d8 x689m1e0 x689m1e8 x689m1f0 x689m208 x689m210 x689m218 x689m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x689rax, hB_x689rax, hE_x689rcx, hB_x689rcx, hE_x689rdx, hB_x689rdx, hE_x689rsi, hB_x689rsi, hE_x689rdi, hB_x689rdi, hE_x689r8, hB_x689r8, hE_x689r9, hB_x689r9, hE_x689r10, hB_x689r10, hE_x689r13, hB_x689r13, hE_x689r15, hB_x689r15, hE_x689m38, hB_x689m38, hE_x689m40, hB_x689m40, hE_x689m68, hB_x689m68, hE_x689m70, hB_x689m70, hE_x689m98, hB_x689m98, hE_x689ma0, hB_x689ma0, hE_x689ma8, hB_x689ma8, hE_x689m150, hB_x689m150, hE_x689m158, hB_x689m158, hE_x689m160, hB_x689m160, hE_x689m168, hB_x689m168, hE_x689m170, hB_x689m170, hE_x689m178, hB_x689m178, hE_x689m180, hB_x689m180, hE_x689m188, hB_x689m188, hE_x689m190, hB_x689m190, hE_x689m198, hB_x689m198, hE_x689m1a0, hB_x689m1a0, hE_x689m1a8, hB_x689m1a8, hE_x689m1b0, hB_x689m1b0, hE_x689m1b8, hB_x689m1b8, hE_x689m1c0, hB_x689m1c0, hE_x689m1c8, hB_x689m1c8, hE_x689m1d0, hB_x689m1d0, hE_x689m1d8, hB_x689m1d8, hE_x689m1e0, hB_x689m1e0, hE_x689m1e8, hB_x689m1e8, hE_x689m1f0, hB_x689m1f0, hE_x689m208, hB_x689m208, hE_x689m210, hB_x689m210, hE_x689m218, hB_x689m218, hE_x689m220, hB_x689m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x689rax, hE_x689rcx, hE_x689rdx, hE_x689rsi, hE_x689rdi, hE_x689r8, hE_x689r9, hE_x689r10, hE_x689r13, hE_x689r15, hE_x689m38, hE_x689m40, hE_x689m68, hE_x689m70, hE_x689m98, hE_x689ma0, hE_x689ma8, hE_x689m150, hE_x689m158, hE_x689m160, hE_x689m168, hE_x689m170, hE_x689m178, hE_x689m180, hE_x689m188, hE_x689m190, hE_x689m198, hE_x689m1a0, hE_x689m1a8, hE_x689m1b0, hE_x689m1b8, hE_x689m1c0, hE_x689m1c8, hE_x689m1d0, hE_x689m1d8, hE_x689m1e0, hE_x689m1e8, hE_x689m1f0, hE_x689m208, hE_x689m210, hE_x689m218, hE_x689m220, hsp4, Nat.mod_eq_of_lt hB_x689rax, Nat.mod_eq_of_lt hB_x689rcx, Nat.mod_eq_of_lt hB_x689rdx, Nat.mod_eq_of_lt hB_x689rsi, Nat.mod_eq_of_lt hB_x689rdi, Nat.mod_eq_of_lt hB_x689r8, Nat.mod_eq_of_lt hB_x689r9, Nat.mod_eq_of_lt hB_x689r10, Nat.mod_eq_of_lt hB_x689r13, Nat.mod_eq_of_lt hB_x689r15, Nat.mod_eq_of_lt hB_x689m38, Nat.mod_eq_of_lt hB_x689m40, Nat.mod_eq_of_lt hB_x689m68, Nat.mod_eq_of_lt hB_x689m70, Nat.mod_eq_of_lt hB_x689m98, Nat.mod_eq_of_lt hB_x689ma0, Nat.mod_eq_of_lt hB_x689ma8, Nat.mod_eq_of_lt hB_x689m150, Nat.mod_eq_of_lt hB_x689m158, Nat.mod_eq_of_lt hB_x689m160, Nat.mod_eq_of_lt hB_x689m168, Nat.mod_eq_of_lt hB_x689m170, Nat.mod_eq_of_lt hB_x689m178, Nat.mod_eq_of_lt hB_x689m180, Nat.mod_eq_of_lt hB_x689m188, Nat.mod_eq_of_lt hB_x689m190, Nat.mod_eq_of_lt hB_x689m198, Nat.mod_eq_of_lt hB_x689m1a0, Nat.mod_eq_of_lt hB_x689m1a8, Nat.mod_eq_of_lt hB_x689m1b0, Nat.mod_eq_of_lt hB_x689m1b8, Nat.mod_eq_of_lt hB_x689m1c0, Nat.mod_eq_of_lt hB_x689m1c8, Nat.mod_eq_of_lt hB_x689m1d0, Nat.mod_eq_of_lt hB_x689m1d8, Nat.mod_eq_of_lt hB_x689m1e0, Nat.mod_eq_of_lt hB_x689m1e8, Nat.mod_eq_of_lt hB_x689m1f0, Nat.mod_eq_of_lt hB_x689m208, Nat.mod_eq_of_lt hB_x689m210, Nat.mod_eq_of_lt hB_x689m218, Nat.mod_eq_of_lt hB_x689m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_689_6b3
  refine ⟨(x689m40 + (x689m1e0 + x689rdx + (x689m1f0 + x689r13 + (x689m1e8 + x689rsi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x689m1e8 + x689rsi) % 18446744073709551616, (x689m1f0 + x689r13 + (x689m1e8 + x689rsi) / 18446744073709551616) % 18446744073709551616, (x689m1e0 + x689rdx + (x689m1f0 + x689r13 + (x689m1e8 + x689rsi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L6b3
    and_intros
    · first | exact hE_x689rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x689rax)
    · exact hB_x689rax
    · first | exact hE_x689rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x689rcx)
    · exact hB_x689rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x689rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x689rdi)
    · exact hB_x689rdi
    · first | exact hE_x689r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x689r8)
    · exact hB_x689r8
    · first | exact hE_x689r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x689r9)
    · exact hB_x689r9
    · first | exact hE_x689r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x689r10)
    · exact hB_x689r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x689r15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x689r15)
    · exact hB_x689r15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m38
    · exact hB_x689m38
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m68
    · exact hB_x689m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m70
    · exact hB_x689m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m98
    · exact hB_x689m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689ma0
    · exact hB_x689ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689ma8
    · exact hB_x689ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m150
    · exact hB_x689m150
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m158
    · exact hB_x689m158
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m160
    · exact hB_x689m160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m168
    · exact hB_x689m168
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m170
    · exact hB_x689m170
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m178
    · exact hB_x689m178
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m180
    · exact hB_x689m180
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m188
    · exact hB_x689m188
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m190
    · exact hB_x689m190
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m198
    · exact hB_x689m198
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1a0
    · exact hB_x689m1a0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1a8
    · exact hB_x689m1a8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1b0
    · exact hB_x689m1b0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1b8
    · exact hB_x689m1b8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1c0
    · exact hB_x689m1c0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1c8
    · exact hB_x689m1c8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1d0
    · exact hB_x689m1d0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m1d8
    · exact hB_x689m1d8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m208
    · exact hB_x689m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m210
    · exact hB_x689m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m218
    · exact hB_x689m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x689m220
    · exact hB_x689m220
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
