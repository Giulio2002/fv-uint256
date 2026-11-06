import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_886_92d (s : State) (y3 : Nat) (x886rax x886rcx x886rbx x886rsi x886rdi x886r8 x886r9 x886r10 x886r11 x886r12 x886r13 x886r15 x886m40 x886m48 x886m50 x886m60 x886m68 x886m70 x886md8 x886me0 x886m100 x886m1f8 x886m200 x886m208 x886m218 x886m220 : Nat) (S' : State) : Prop :=
  ∃ x92dr11 x92dmc8 x92dmd0 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x92dm210, L92d s S' x886rcx x886rbx x886rsi x886rdi x886r8 x886r9 x886r10 x92dr11 x886r12 x886r13 x886r15 x886m40 x886m48 x886m50 x886m60 x886m68 x886m70 x92dmc8 x92dmd0 x886md8 x886me0 x886m100 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x886m1f8 x886m200 x886m208 x92dm210 x886m218 x886m220 ∧ x92dr11 = (x886r9 * x886r11) % 18446744073709551616 ∧ x92dmc8 = (x886rsi * x886m218 / 18446744073709551616) % 18446744073709551616 ∧ x92dmd0 = (x886rsi * x886r11 / 18446744073709551616) % 18446744073709551616 ∧ x92dm1a8 = (x886rsi * x886m218) % 18446744073709551616 ∧ x92dm1b0 = (x886r8 * x886m218) % 18446744073709551616 ∧ x92dm1b8 = (x886r8 * x886m218 / 18446744073709551616) % 18446744073709551616 ∧ x92dm1c0 = (x886m218 * x886rdi) % 18446744073709551616 ∧ x92dm1c8 = (x886m218 * x886rdi / 18446744073709551616) % 18446744073709551616 ∧ x92dm1d0 = (x886r9 * x886r11 / 18446744073709551616) % 18446744073709551616 ∧ x92dm1d8 = (x886rbx * x886r11) % 18446744073709551616 ∧ x92dm1e0 = (x886rbx * x886r11 / 18446744073709551616) % 18446744073709551616 ∧ x92dm1e8 = (x886rsi * x886r11) % 18446744073709551616 ∧ x92dm1f0 = (x886rax * x886r11) % 18446744073709551616 ∧ x92dm210 = (x886rax * x886r11 / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_886_92d {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x886)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x886rax x886rcx x886rbx x886rsi x886rdi x886r8 x886r9 x886r10 x886r11 x886r12 x886r13 x886r15 x886m40 x886m48 x886m50 x886m60 x886m68 x886m70 x886md8 x886me0 x886m100 x886m1f8 x886m200 x886m208 x886m218 x886m220 : Nat) (hL : L886 s S x886rax x886rcx x886rbx x886rsi x886rdi x886r8 x886r9 x886r10 x886r11 x886r12 x886r13 x886r15 x886m40 x886m48 x886m50 x886m60 x886m68 x886m70 x886md8 x886me0 x886m100 x886m1f8 x886m200 x886m208 x886m218 x886m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x92d)) S (P_886_92d s y3 x886rax x886rcx x886rbx x886rsi x886rdi x886r8 x886r9 x886r10 x886r11 x886r12 x886r13 x886r15 x886m40 x886m48 x886m50 x886m60 x886m68 x886m70 x886md8 x886me0 x886m100 x886m1f8 x886m200 x886m208 x886m218 x886m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x886rax, hB_x886rax, hE_x886rcx, hB_x886rcx, hE_x886rbx, hB_x886rbx, hE_x886rsi, hB_x886rsi, hE_x886rdi, hB_x886rdi, hE_x886r8, hB_x886r8, hE_x886r9, hB_x886r9, hE_x886r10, hB_x886r10, hE_x886r11, hB_x886r11, hE_x886r12, hB_x886r12, hE_x886r13, hB_x886r13, hE_x886r15, hB_x886r15, hE_x886m40, hB_x886m40, hE_x886m48, hB_x886m48, hE_x886m50, hB_x886m50, hE_x886m60, hB_x886m60, hE_x886m68, hB_x886m68, hE_x886m70, hB_x886m70, hE_x886md8, hB_x886md8, hE_x886me0, hB_x886me0, hE_x886m100, hB_x886m100, hE_x886m1f8, hB_x886m1f8, hE_x886m200, hB_x886m200, hE_x886m208, hB_x886m208, hE_x886m218, hB_x886m218, hE_x886m220, hB_x886m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x886rax, hE_x886rcx, hE_x886rbx, hE_x886rsi, hE_x886rdi, hE_x886r8, hE_x886r9, hE_x886r10, hE_x886r11, hE_x886r12, hE_x886r13, hE_x886r15, hE_x886m40, hE_x886m48, hE_x886m50, hE_x886m60, hE_x886m68, hE_x886m70, hE_x886md8, hE_x886me0, hE_x886m100, hE_x886m1f8, hE_x886m200, hE_x886m208, hE_x886m218, hE_x886m220, hsp4, Nat.mod_eq_of_lt hB_x886rax, Nat.mod_eq_of_lt hB_x886rcx, Nat.mod_eq_of_lt hB_x886rbx, Nat.mod_eq_of_lt hB_x886rsi, Nat.mod_eq_of_lt hB_x886rdi, Nat.mod_eq_of_lt hB_x886r8, Nat.mod_eq_of_lt hB_x886r9, Nat.mod_eq_of_lt hB_x886r10, Nat.mod_eq_of_lt hB_x886r11, Nat.mod_eq_of_lt hB_x886r12, Nat.mod_eq_of_lt hB_x886r13, Nat.mod_eq_of_lt hB_x886r15, Nat.mod_eq_of_lt hB_x886m40, Nat.mod_eq_of_lt hB_x886m48, Nat.mod_eq_of_lt hB_x886m50, Nat.mod_eq_of_lt hB_x886m60, Nat.mod_eq_of_lt hB_x886m68, Nat.mod_eq_of_lt hB_x886m70, Nat.mod_eq_of_lt hB_x886md8, Nat.mod_eq_of_lt hB_x886me0, Nat.mod_eq_of_lt hB_x886m100, Nat.mod_eq_of_lt hB_x886m1f8, Nat.mod_eq_of_lt hB_x886m200, Nat.mod_eq_of_lt hB_x886m208, Nat.mod_eq_of_lt hB_x886m218, Nat.mod_eq_of_lt hB_x886m220]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_886_92d
  refine ⟨(x886r9 * x886r11) % 18446744073709551616, (x886rsi * x886m218 / 18446744073709551616) % 18446744073709551616, (x886rsi * x886r11 / 18446744073709551616) % 18446744073709551616, (x886rsi * x886m218) % 18446744073709551616, (x886r8 * x886m218) % 18446744073709551616, (x886r8 * x886m218 / 18446744073709551616) % 18446744073709551616, (x886m218 * x886rdi) % 18446744073709551616, (x886m218 * x886rdi / 18446744073709551616) % 18446744073709551616, (x886r9 * x886r11 / 18446744073709551616) % 18446744073709551616, (x886rbx * x886r11) % 18446744073709551616, (x886rbx * x886r11 / 18446744073709551616) % 18446744073709551616, (x886rsi * x886r11) % 18446744073709551616, (x886rax * x886r11) % 18446744073709551616, (x886rax * x886r11 / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L92d
    and_intros
    · first | exact hE_x886rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886rcx)
    · exact hB_x886rcx
    · first | exact hE_x886rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886rbx)
    · exact hB_x886rbx
    · first | exact hE_x886rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886rsi)
    · exact hB_x886rsi
    · first | exact hE_x886rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886rdi)
    · exact hB_x886rdi
    · first | exact hE_x886r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886r8)
    · exact hB_x886r8
    · first | exact hE_x886r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886r9)
    · exact hB_x886r9
    · first | exact hE_x886r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886r10)
    · exact hB_x886r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x886r12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886r12)
    · exact hB_x886r12
    · first | exact hE_x886r13 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886r13)
    · exact hB_x886r13
    · first | exact hE_x886r15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x886r15)
    · exact hB_x886r15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m40
    · exact hB_x886m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m48
    · exact hB_x886m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m50
    · exact hB_x886m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m60
    · exact hB_x886m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m68
    · exact hB_x886m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m70
    · exact hB_x886m70
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886md8
    · exact hB_x886md8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886me0
    · exact hB_x886me0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m100
    · exact hB_x886m100
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
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m1f8
    · exact hB_x886m1f8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m200
    · exact hB_x886m200
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m208
    · exact hB_x886m208
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m218
    · exact hB_x886m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x886m220
    · exact hB_x886m220
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
