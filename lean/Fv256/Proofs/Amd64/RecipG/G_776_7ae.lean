import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_776_7ae (s : State) (y3 : Nat) (x776rax x776rcx x776rbx x776rsi x776rdi x776r8 x776r9 x776r10 x776r13 x776m68 x776m70 x776m98 x776ma0 x776ma8 x776m150 x776m158 x776m160 x776m208 x776m210 x776m218 x776m220 : Nat) (S' : State) : Prop :=
  ∃ x7aerax x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11, L7ae s S' x7aerax x776rcx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x776m98 x776ma0 x776ma8 x776m208 x776m210 x776m218 x776m220 ∧ x7aerax = (x776rax + x776r9 + (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x7aerdx = (x776m70 + x776r13) % 18446744073709551616 ∧ x7aerbx = (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x7aersi = (x776m150 + x776r10 + (x776rax + x776r9 + (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x7aerdi = (x776rdi + (x776m150 + x776r10 + (x776rax + x776r9 + (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x7aer8 = (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x7aer11 = (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_776_7ae {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x776)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x776rax x776rcx x776rbx x776rsi x776rdi x776r8 x776r9 x776r10 x776r13 x776m68 x776m70 x776m98 x776ma0 x776ma8 x776m150 x776m158 x776m160 x776m208 x776m210 x776m218 x776m220 : Nat) (hL : L776 s S x776rax x776rcx x776rbx x776rsi x776rdi x776r8 x776r9 x776r10 x776r13 x776m68 x776m70 x776m98 x776ma0 x776ma8 x776m150 x776m158 x776m160 x776m208 x776m210 x776m218 x776m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x7ae)) S (P_776_7ae s y3 x776rax x776rcx x776rbx x776rsi x776rdi x776r8 x776r9 x776r10 x776r13 x776m68 x776m70 x776m98 x776ma0 x776ma8 x776m150 x776m158 x776m160 x776m208 x776m210 x776m218 x776m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x776rax, hB_x776rax, hE_x776rcx, hB_x776rcx, hE_x776rbx, hB_x776rbx, hE_x776rsi, hB_x776rsi, hE_x776rdi, hB_x776rdi, hE_x776r8, hB_x776r8, hE_x776r9, hB_x776r9, hE_x776r10, hB_x776r10, hE_x776r13, hB_x776r13, hE_x776m68, hB_x776m68, hE_x776m70, hB_x776m70, hE_x776m98, hB_x776m98, hE_x776ma0, hB_x776ma0, hE_x776ma8, hB_x776ma8, hE_x776m150, hB_x776m150, hE_x776m158, hB_x776m158, hE_x776m160, hB_x776m160, hE_x776m208, hB_x776m208, hE_x776m210, hB_x776m210, hE_x776m218, hB_x776m218, hE_x776m220, hB_x776m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x776rax, hE_x776rcx, hE_x776rbx, hE_x776rsi, hE_x776rdi, hE_x776r8, hE_x776r9, hE_x776r10, hE_x776r13, hE_x776m68, hE_x776m70, hE_x776m98, hE_x776ma0, hE_x776ma8, hE_x776m150, hE_x776m158, hE_x776m160, hE_x776m208, hE_x776m210, hE_x776m218, hE_x776m220, hsp4, Nat.mod_eq_of_lt hB_x776rax, Nat.mod_eq_of_lt hB_x776rcx, Nat.mod_eq_of_lt hB_x776rbx, Nat.mod_eq_of_lt hB_x776rsi, Nat.mod_eq_of_lt hB_x776rdi, Nat.mod_eq_of_lt hB_x776r8, Nat.mod_eq_of_lt hB_x776r9, Nat.mod_eq_of_lt hB_x776r10, Nat.mod_eq_of_lt hB_x776r13, Nat.mod_eq_of_lt hB_x776m68, Nat.mod_eq_of_lt hB_x776m70, Nat.mod_eq_of_lt hB_x776m98, Nat.mod_eq_of_lt hB_x776ma0, Nat.mod_eq_of_lt hB_x776ma8, Nat.mod_eq_of_lt hB_x776m150, Nat.mod_eq_of_lt hB_x776m158, Nat.mod_eq_of_lt hB_x776m160, Nat.mod_eq_of_lt hB_x776m208, Nat.mod_eq_of_lt hB_x776m210, Nat.mod_eq_of_lt hB_x776m218, Nat.mod_eq_of_lt hB_x776m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_776_7ae
  refine ⟨(x776rax + x776r9 + (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x776m70 + x776r13) % 18446744073709551616, (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x776m150 + x776r10 + (x776rax + x776r9 + (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x776rdi + (x776m150 + x776r10 + (x776rax + x776r9 + (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x776m160 + x776rsi + (x776m158 + x776r8 + (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x776m68 + x776rbx + (x776m70 + x776r13) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L7ae
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x776rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x776rcx)
    · exact hB_x776rcx
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
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x776m98
    · exact hB_x776m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x776ma0
    · exact hB_x776ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x776ma8
    · exact hB_x776ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x776m208
    · exact hB_x776m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x776m210
    · exact hB_x776m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x776m218
    · exact hB_x776m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x776m220
    · exact hB_x776m220
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
