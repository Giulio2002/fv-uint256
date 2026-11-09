import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_549_5e2 (s : State) (y3 : Nat) (x549rax x549rcx x549rbx x549rsi x549rdi x549r8 x549r9 x549r10 x549r13 x549r15 x549m48 x549m50 x549m58 x549m68 x549m70 x549m98 x549ma0 x549ma8 x549m1f8 x549m200 x549m208 x549m210 x549m218 x549m220 : Nat) (S' : State) : Prop :=
  ∃ x5e2r13 x5e2m38 x5e2m40 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0, L5e2 s S' x549rcx x549rbx x549rsi x549rdi x549r8 x549r9 x549r10 x5e2r13 x549r15 x5e2m38 x5e2m40 x549m48 x549m50 x549m58 x549m68 x549m70 x549m98 x549ma0 x549ma8 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x549m1f8 x549m200 x549m208 x549m210 x549m218 x549m220 ∧ x5e2r13 = x549m218 % 18446744073709551616 ∧ x5e2m38 = (x549r9 * x549m218 / 18446744073709551616) % 18446744073709551616 ∧ x5e2m40 = (x549r9 * x549r13 / 18446744073709551616) % 18446744073709551616 ∧ x5e2m198 = (x549r9 * x549m218) % 18446744073709551616 ∧ x5e2m1a0 = (x549r8 * x549m218) % 18446744073709551616 ∧ x5e2m1a8 = (x549r8 * x549m218 / 18446744073709551616) % 18446744073709551616 ∧ x5e2m1b0 = (x549r10 * x549m218) % 18446744073709551616 ∧ x5e2m1b8 = (x549r10 * x549m218 / 18446744073709551616) % 18446744073709551616 ∧ x5e2m1c0 = (x549rbx * x549r13) % 18446744073709551616 ∧ x5e2m1c8 = (x549rbx * x549r13 / 18446744073709551616) % 18446744073709551616 ∧ x5e2m1d0 = (x549rdi * x549r13) % 18446744073709551616 ∧ x5e2m1d8 = (x549rdi * x549r13 / 18446744073709551616) % 18446744073709551616 ∧ x5e2m1e0 = (x549r9 * x549r13) % 18446744073709551616 ∧ x5e2m1e8 = (x549rax * x549r13) % 18446744073709551616 ∧ x5e2m1f0 = (x549rax * x549r13 / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_549_5e2 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x549)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x549rax x549rcx x549rbx x549rsi x549rdi x549r8 x549r9 x549r10 x549r13 x549r15 x549m48 x549m50 x549m58 x549m68 x549m70 x549m98 x549ma0 x549ma8 x549m1f8 x549m200 x549m208 x549m210 x549m218 x549m220 : Nat) (hL : L549 s S x549rax x549rcx x549rbx x549rsi x549rdi x549r8 x549r9 x549r10 x549r13 x549r15 x549m48 x549m50 x549m58 x549m68 x549m70 x549m98 x549ma0 x549ma8 x549m1f8 x549m200 x549m208 x549m210 x549m218 x549m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x5e2)) S (P_549_5e2 s y3 x549rax x549rcx x549rbx x549rsi x549rdi x549r8 x549r9 x549r10 x549r13 x549r15 x549m48 x549m50 x549m58 x549m68 x549m70 x549m98 x549ma0 x549ma8 x549m1f8 x549m200 x549m208 x549m210 x549m218 x549m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x549rax, hB_x549rax, hE_x549rcx, hB_x549rcx, hE_x549rbx, hB_x549rbx, hE_x549rsi, hB_x549rsi, hE_x549rdi, hB_x549rdi, hE_x549r8, hB_x549r8, hE_x549r9, hB_x549r9, hE_x549r10, hB_x549r10, hE_x549r13, hB_x549r13, hE_x549r15, hB_x549r15, hE_x549m48, hB_x549m48, hE_x549m50, hB_x549m50, hE_x549m58, hB_x549m58, hE_x549m68, hB_x549m68, hE_x549m70, hB_x549m70, hE_x549m98, hB_x549m98, hE_x549ma0, hB_x549ma0, hE_x549ma8, hB_x549ma8, hE_x549m1f8, hB_x549m1f8, hE_x549m200, hB_x549m200, hE_x549m208, hB_x549m208, hE_x549m210, hB_x549m210, hE_x549m218, hB_x549m218, hE_x549m220, hB_x549m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x549rax, hE_x549rcx, hE_x549rbx, hE_x549rsi, hE_x549rdi, hE_x549r8, hE_x549r9, hE_x549r10, hE_x549r13, hE_x549r15, hE_x549m48, hE_x549m50, hE_x549m58, hE_x549m68, hE_x549m70, hE_x549m98, hE_x549ma0, hE_x549ma8, hE_x549m1f8, hE_x549m200, hE_x549m208, hE_x549m210, hE_x549m218, hE_x549m220, hsp4, Nat.mod_eq_of_lt hB_x549rax, Nat.mod_eq_of_lt hB_x549rcx, Nat.mod_eq_of_lt hB_x549rbx, Nat.mod_eq_of_lt hB_x549rsi, Nat.mod_eq_of_lt hB_x549rdi, Nat.mod_eq_of_lt hB_x549r8, Nat.mod_eq_of_lt hB_x549r9, Nat.mod_eq_of_lt hB_x549r10, Nat.mod_eq_of_lt hB_x549r13, Nat.mod_eq_of_lt hB_x549r15, Nat.mod_eq_of_lt hB_x549m48, Nat.mod_eq_of_lt hB_x549m50, Nat.mod_eq_of_lt hB_x549m58, Nat.mod_eq_of_lt hB_x549m68, Nat.mod_eq_of_lt hB_x549m70, Nat.mod_eq_of_lt hB_x549m98, Nat.mod_eq_of_lt hB_x549ma0, Nat.mod_eq_of_lt hB_x549ma8, Nat.mod_eq_of_lt hB_x549m1f8, Nat.mod_eq_of_lt hB_x549m200, Nat.mod_eq_of_lt hB_x549m208, Nat.mod_eq_of_lt hB_x549m210, Nat.mod_eq_of_lt hB_x549m218, Nat.mod_eq_of_lt hB_x549m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_549_5e2
  refine ⟨x549m218 % 18446744073709551616, (x549r9 * x549m218 / 18446744073709551616) % 18446744073709551616, (x549r9 * x549r13 / 18446744073709551616) % 18446744073709551616, (x549r9 * x549m218) % 18446744073709551616, (x549r8 * x549m218) % 18446744073709551616, (x549r8 * x549m218 / 18446744073709551616) % 18446744073709551616, (x549r10 * x549m218) % 18446744073709551616, (x549r10 * x549m218 / 18446744073709551616) % 18446744073709551616, (x549rbx * x549r13) % 18446744073709551616, (x549rbx * x549r13 / 18446744073709551616) % 18446744073709551616, (x549rdi * x549r13) % 18446744073709551616, (x549rdi * x549r13 / 18446744073709551616) % 18446744073709551616, (x549r9 * x549r13) % 18446744073709551616, (x549rax * x549r13) % 18446744073709551616, (x549rax * x549r13 / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L5e2
    and_intros
    · first | exact hE_x549rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549rcx)
    · exact hB_x549rcx
    · first | exact hE_x549rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549rbx)
    · exact hB_x549rbx
    · first | exact hE_x549rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549rsi)
    · exact hB_x549rsi
    · first | exact hE_x549rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549rdi)
    · exact hB_x549rdi
    · first | exact hE_x549r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549r8)
    · exact hB_x549r8
    · first | exact hE_x549r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549r9)
    · exact hB_x549r9
    · first | exact hE_x549r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549r10)
    · exact hB_x549r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x549r15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x549r15)
    · exact hB_x549r15
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m48
    · exact hB_x549m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m50
    · exact hB_x549m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m58
    · exact hB_x549m58
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m68
    · exact hB_x549m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m70
    · exact hB_x549m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m98
    · exact hB_x549m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549ma0
    · exact hB_x549ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549ma8
    · exact hB_x549ma8
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m1f8
    · exact hB_x549m1f8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m200
    · exact hB_x549m200
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m208
    · exact hB_x549m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m210
    · exact hB_x549m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m218
    · exact hB_x549m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x549m220
    · exact hB_x549m220
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
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
