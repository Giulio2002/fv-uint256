import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_5e2_660 (s : State) (y3 : Nat) (x5e2rcx x5e2rbx x5e2rsi x5e2rdi x5e2r8 x5e2r9 x5e2r10 x5e2r13 x5e2r15 x5e2m38 x5e2m40 x5e2m48 x5e2m50 x5e2m58 x5e2m68 x5e2m70 x5e2m98 x5e2ma0 x5e2ma8 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x5e2m1f8 x5e2m200 x5e2m208 x5e2m210 x5e2m218 x5e2m220 : Nat) (S' : State) : Prop :=
  ∃ x660rax x660rdi x660r8 x660r9 x660r10 x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190, L660 s S' x660rax x5e2rcx x660rdi x660r8 x660r9 x660r10 x5e2r15 x5e2m38 x5e2m40 x5e2m48 x5e2m50 x5e2m58 x5e2m68 x5e2m70 x5e2m98 x5e2ma0 x5e2ma8 x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x5e2m1f8 x5e2m200 x5e2m208 x5e2m210 x5e2m218 x5e2m220 ∧ x660rax = (x5e2rbx * x5e2rsi) % 18446744073709551616 ∧ x660rdi = (x5e2r9 * x5e2rsi / 18446744073709551616) % 18446744073709551616 ∧ x660r8 = (x5e2r10 * x5e2rsi / 18446744073709551616) % 18446744073709551616 ∧ x660r9 = (x5e2r8 * x5e2rsi / 18446744073709551616) % 18446744073709551616 ∧ x660r10 = (x5e2rbx * x5e2r13 / 18446744073709551616) % 18446744073709551616 ∧ x660m150 = (x5e2rbx * x5e2rsi / 18446744073709551616) % 18446744073709551616 ∧ x660m158 = (x5e2rdi * x5e2rsi) % 18446744073709551616 ∧ x660m160 = (x5e2rdi * x5e2rsi / 18446744073709551616) % 18446744073709551616 ∧ x660m168 = (x5e2r9 * x5e2rsi) % 18446744073709551616 ∧ x660m170 = (x5e2r8 * x5e2rsi) % 18446744073709551616 ∧ x660m178 = (x5e2r10 * x5e2rsi) % 18446744073709551616 ∧ x660m180 = (x5e2rbx * x5e2r13) % 18446744073709551616 ∧ x660m188 = (x5e2rdi * x5e2r13) % 18446744073709551616 ∧ x660m190 = (x5e2rdi * x5e2r13 / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_5e2_660 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x5e2)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x5e2rcx x5e2rbx x5e2rsi x5e2rdi x5e2r8 x5e2r9 x5e2r10 x5e2r13 x5e2r15 x5e2m38 x5e2m40 x5e2m48 x5e2m50 x5e2m58 x5e2m68 x5e2m70 x5e2m98 x5e2ma0 x5e2ma8 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x5e2m1f8 x5e2m200 x5e2m208 x5e2m210 x5e2m218 x5e2m220 : Nat) (hL : L5e2 s S x5e2rcx x5e2rbx x5e2rsi x5e2rdi x5e2r8 x5e2r9 x5e2r10 x5e2r13 x5e2r15 x5e2m38 x5e2m40 x5e2m48 x5e2m50 x5e2m58 x5e2m68 x5e2m70 x5e2m98 x5e2ma0 x5e2ma8 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x5e2m1f8 x5e2m200 x5e2m208 x5e2m210 x5e2m218 x5e2m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x660)) S (P_5e2_660 s y3 x5e2rcx x5e2rbx x5e2rsi x5e2rdi x5e2r8 x5e2r9 x5e2r10 x5e2r13 x5e2r15 x5e2m38 x5e2m40 x5e2m48 x5e2m50 x5e2m58 x5e2m68 x5e2m70 x5e2m98 x5e2ma0 x5e2ma8 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x5e2m1f8 x5e2m200 x5e2m208 x5e2m210 x5e2m218 x5e2m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x5e2rcx, hB_x5e2rcx, hE_x5e2rbx, hB_x5e2rbx, hE_x5e2rsi, hB_x5e2rsi, hE_x5e2rdi, hB_x5e2rdi, hE_x5e2r8, hB_x5e2r8, hE_x5e2r9, hB_x5e2r9, hE_x5e2r10, hB_x5e2r10, hE_x5e2r13, hB_x5e2r13, hE_x5e2r15, hB_x5e2r15, hE_x5e2m38, hB_x5e2m38, hE_x5e2m40, hB_x5e2m40, hE_x5e2m48, hB_x5e2m48, hE_x5e2m50, hB_x5e2m50, hE_x5e2m58, hB_x5e2m58, hE_x5e2m68, hB_x5e2m68, hE_x5e2m70, hB_x5e2m70, hE_x5e2m98, hB_x5e2m98, hE_x5e2ma0, hB_x5e2ma0, hE_x5e2ma8, hB_x5e2ma8, hE_x5e2m198, hB_x5e2m198, hE_x5e2m1a0, hB_x5e2m1a0, hE_x5e2m1a8, hB_x5e2m1a8, hE_x5e2m1b0, hB_x5e2m1b0, hE_x5e2m1b8, hB_x5e2m1b8, hE_x5e2m1c0, hB_x5e2m1c0, hE_x5e2m1c8, hB_x5e2m1c8, hE_x5e2m1d0, hB_x5e2m1d0, hE_x5e2m1d8, hB_x5e2m1d8, hE_x5e2m1e0, hB_x5e2m1e0, hE_x5e2m1e8, hB_x5e2m1e8, hE_x5e2m1f0, hB_x5e2m1f0, hE_x5e2m1f8, hB_x5e2m1f8, hE_x5e2m200, hB_x5e2m200, hE_x5e2m208, hB_x5e2m208, hE_x5e2m210, hB_x5e2m210, hE_x5e2m218, hB_x5e2m218, hE_x5e2m220, hB_x5e2m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x5e2rcx, hE_x5e2rbx, hE_x5e2rsi, hE_x5e2rdi, hE_x5e2r8, hE_x5e2r9, hE_x5e2r10, hE_x5e2r13, hE_x5e2r15, hE_x5e2m38, hE_x5e2m40, hE_x5e2m48, hE_x5e2m50, hE_x5e2m58, hE_x5e2m68, hE_x5e2m70, hE_x5e2m98, hE_x5e2ma0, hE_x5e2ma8, hE_x5e2m198, hE_x5e2m1a0, hE_x5e2m1a8, hE_x5e2m1b0, hE_x5e2m1b8, hE_x5e2m1c0, hE_x5e2m1c8, hE_x5e2m1d0, hE_x5e2m1d8, hE_x5e2m1e0, hE_x5e2m1e8, hE_x5e2m1f0, hE_x5e2m1f8, hE_x5e2m200, hE_x5e2m208, hE_x5e2m210, hE_x5e2m218, hE_x5e2m220, hsp4, Nat.mod_eq_of_lt hB_x5e2rcx, Nat.mod_eq_of_lt hB_x5e2rbx, Nat.mod_eq_of_lt hB_x5e2rsi, Nat.mod_eq_of_lt hB_x5e2rdi, Nat.mod_eq_of_lt hB_x5e2r8, Nat.mod_eq_of_lt hB_x5e2r9, Nat.mod_eq_of_lt hB_x5e2r10, Nat.mod_eq_of_lt hB_x5e2r13, Nat.mod_eq_of_lt hB_x5e2r15, Nat.mod_eq_of_lt hB_x5e2m38, Nat.mod_eq_of_lt hB_x5e2m40, Nat.mod_eq_of_lt hB_x5e2m48, Nat.mod_eq_of_lt hB_x5e2m50, Nat.mod_eq_of_lt hB_x5e2m58, Nat.mod_eq_of_lt hB_x5e2m68, Nat.mod_eq_of_lt hB_x5e2m70, Nat.mod_eq_of_lt hB_x5e2m98, Nat.mod_eq_of_lt hB_x5e2ma0, Nat.mod_eq_of_lt hB_x5e2ma8, Nat.mod_eq_of_lt hB_x5e2m198, Nat.mod_eq_of_lt hB_x5e2m1a0, Nat.mod_eq_of_lt hB_x5e2m1a8, Nat.mod_eq_of_lt hB_x5e2m1b0, Nat.mod_eq_of_lt hB_x5e2m1b8, Nat.mod_eq_of_lt hB_x5e2m1c0, Nat.mod_eq_of_lt hB_x5e2m1c8, Nat.mod_eq_of_lt hB_x5e2m1d0, Nat.mod_eq_of_lt hB_x5e2m1d8, Nat.mod_eq_of_lt hB_x5e2m1e0, Nat.mod_eq_of_lt hB_x5e2m1e8, Nat.mod_eq_of_lt hB_x5e2m1f0, Nat.mod_eq_of_lt hB_x5e2m1f8, Nat.mod_eq_of_lt hB_x5e2m200, Nat.mod_eq_of_lt hB_x5e2m208, Nat.mod_eq_of_lt hB_x5e2m210, Nat.mod_eq_of_lt hB_x5e2m218, Nat.mod_eq_of_lt hB_x5e2m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_5e2_660
  refine ⟨(x5e2rbx * x5e2rsi) % 18446744073709551616, (x5e2r9 * x5e2rsi / 18446744073709551616) % 18446744073709551616, (x5e2r10 * x5e2rsi / 18446744073709551616) % 18446744073709551616, (x5e2r8 * x5e2rsi / 18446744073709551616) % 18446744073709551616, (x5e2rbx * x5e2r13 / 18446744073709551616) % 18446744073709551616, (x5e2rbx * x5e2rsi / 18446744073709551616) % 18446744073709551616, (x5e2rdi * x5e2rsi) % 18446744073709551616, (x5e2rdi * x5e2rsi / 18446744073709551616) % 18446744073709551616, (x5e2r9 * x5e2rsi) % 18446744073709551616, (x5e2r8 * x5e2rsi) % 18446744073709551616, (x5e2r10 * x5e2rsi) % 18446744073709551616, (x5e2rbx * x5e2r13) % 18446744073709551616, (x5e2rdi * x5e2r13) % 18446744073709551616, (x5e2rdi * x5e2r13 / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L660
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x5e2rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x5e2rcx)
    · exact hB_x5e2rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x5e2r15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x5e2r15)
    · exact hB_x5e2r15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m38
    · exact hB_x5e2m38
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m40
    · exact hB_x5e2m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m48
    · exact hB_x5e2m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m50
    · exact hB_x5e2m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m58
    · exact hB_x5e2m58
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m68
    · exact hB_x5e2m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m70
    · exact hB_x5e2m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m98
    · exact hB_x5e2m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2ma0
    · exact hB_x5e2ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2ma8
    · exact hB_x5e2ma8
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m198
    · exact hB_x5e2m198
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1a0
    · exact hB_x5e2m1a0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1a8
    · exact hB_x5e2m1a8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1b0
    · exact hB_x5e2m1b0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1b8
    · exact hB_x5e2m1b8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1c0
    · exact hB_x5e2m1c0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1c8
    · exact hB_x5e2m1c8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1d0
    · exact hB_x5e2m1d0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1d8
    · exact hB_x5e2m1d8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1e0
    · exact hB_x5e2m1e0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1e8
    · exact hB_x5e2m1e8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1f0
    · exact hB_x5e2m1f0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m1f8
    · exact hB_x5e2m1f8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m200
    · exact hB_x5e2m200
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m208
    · exact hB_x5e2m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m210
    · exact hB_x5e2m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m218
    · exact hB_x5e2m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x5e2m220
    · exact hB_x5e2m220
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
