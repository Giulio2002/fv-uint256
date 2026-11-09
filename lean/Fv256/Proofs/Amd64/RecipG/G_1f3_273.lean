import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_1f3_273 (s : State) (y3 : Nat) (x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220 : Nat) (S' : State) : Prop :=
  ∃ x273rax x273rbx x273r10 x273r11 x273r12 x273r13 x273r15 x273mb8 x273m100, L273 s S' x273rax x1f3rcx x273rbx x1f3rsi x1f3rdi x1f3r8 x273r10 x273r11 x273r12 x273r13 x273r15 x1f3mb0 x273mb8 x273m100 x1f3m208 x1f3m210 x1f3m218 x1f3m220 ∧ x273rax = x1f3r9 % 18446744073709551616 ∧ x273rbx = (x1f3r10 * x1f3r10 / 18446744073709551616 + (x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616 + ((x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + ((x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x273r10 = ((x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + ((x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x273r11 = (x1f3rax * x1f3rax % 18446744073709551616 * x1f3rdi / 18446744073709551616) % 18446744073709551616 ∧ x273r12 = (x1f3rax * x1f3rax / 18446744073709551616 + (x1f3r10 * x1f3rax + x1f3r10 * x1f3rax)) % 18446744073709551616 ∧ x273r13 = (x1f3rax * x1f3rax % 18446744073709551616 * x1f3rsi) % 18446744073709551616 ∧ x273r15 = (x1f3rax * x1f3rax % 18446744073709551616 * x1f3rsi / 18446744073709551616) % 18446744073709551616 ∧ x273mb8 = x1f3r10 % 18446744073709551616 ∧ x273m100 = (x1f3r9 * (((x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + ((x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_1f3_273 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x1f3)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220 : Nat) (hL : L1f3 s S x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x273)) S (P_1f3_273 s y3 x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x1f3rax, hB_x1f3rax, hE_x1f3rcx, hB_x1f3rcx, hE_x1f3rsi, hB_x1f3rsi, hE_x1f3rdi, hB_x1f3rdi, hE_x1f3r8, hB_x1f3r8, hE_x1f3r9, hB_x1f3r9, hE_x1f3r10, hB_x1f3r10, hE_x1f3mb0, hB_x1f3mb0, hE_x1f3m208, hB_x1f3m208, hE_x1f3m210, hB_x1f3m210, hE_x1f3m218, hB_x1f3m218, hE_x1f3m220, hB_x1f3m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x1f3rax, hE_x1f3rcx, hE_x1f3rsi, hE_x1f3rdi, hE_x1f3r8, hE_x1f3r9, hE_x1f3r10, hE_x1f3mb0, hE_x1f3m208, hE_x1f3m210, hE_x1f3m218, hE_x1f3m220, hsp4, Nat.mod_eq_of_lt hB_x1f3rax, Nat.mod_eq_of_lt hB_x1f3rcx, Nat.mod_eq_of_lt hB_x1f3rsi, Nat.mod_eq_of_lt hB_x1f3rdi, Nat.mod_eq_of_lt hB_x1f3r8, Nat.mod_eq_of_lt hB_x1f3r9, Nat.mod_eq_of_lt hB_x1f3r10, Nat.mod_eq_of_lt hB_x1f3mb0, Nat.mod_eq_of_lt hB_x1f3m208, Nat.mod_eq_of_lt hB_x1f3m210, Nat.mod_eq_of_lt hB_x1f3m218, Nat.mod_eq_of_lt hB_x1f3m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (
  unfold P_1f3_273
  refine ⟨x1f3r9 % 18446744073709551616, (x1f3r10 * x1f3r10 / 18446744073709551616 + (x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616 + ((x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + ((x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ((x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + ((x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x1f3rax * x1f3rax % 18446744073709551616 * x1f3rdi / 18446744073709551616) % 18446744073709551616, (x1f3rax * x1f3rax / 18446744073709551616 + (x1f3r10 * x1f3rax + x1f3r10 * x1f3rax)) % 18446744073709551616, (x1f3rax * x1f3rax % 18446744073709551616 * x1f3rsi) % 18446744073709551616, (x1f3rax * x1f3rax % 18446744073709551616 * x1f3rsi / 18446744073709551616) % 18446744073709551616, x1f3r10 % 18446744073709551616, (x1f3r9 * (((x1f3r10 * x1f3r10 % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + (x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax / 18446744073709551616 + ((x1f3rax * x1f3rax / 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) % 18446744073709551616 + x1f3r10 * x1f3rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L273
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x1f3rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f3rcx)
    · exact hB_x1f3rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x1f3rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f3rsi)
    · exact hB_x1f3rsi
    · first | exact hE_x1f3rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f3rdi)
    · exact hB_x1f3rdi
    · first | exact hE_x1f3r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f3r8)
    · exact hB_x1f3r8
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
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f3mb0
    · exact hB_x1f3mb0
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f3m208
    · exact hB_x1f3m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f3m210
    · exact hB_x1f3m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f3m218
    · exact hB_x1f3m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f3m220
    · exact hB_x1f3m220
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
