import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_1d0_1f3 (s : State) (y3 : Nat) (x1d0rcx x1d0rbx x1d0rsi x1d0rdi x1d0r8 x1d0r9 x1d0r10 x1d0r11 x1d0m208 x1d0m210 x1d0m218 x1d0m220 : Nat) (S' : State) : Prop :=
  ∃ x1f3rax x1f3r10 x1f3mb0, L1f3 s S' x1f3rax x1d0rcx x1d0rsi x1d0rdi x1d0r8 x1d0r9 x1f3r10 x1f3mb0 x1d0m208 x1d0m210 x1d0m218 x1d0m220 ∧ x1f3rax = (if (BitVec.ofNat 64 x1d0rbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r11).toNat ∧ x1f3r10 = (if (BitVec.ofNat 64 x1d0rbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r10).toNat ∧ x1f3mb0 = ((if (BitVec.ofNat 64 x1d0rbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r11).toNat) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_1d0_1f3 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x1d0)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x1d0rcx x1d0rbx x1d0rsi x1d0rdi x1d0r8 x1d0r9 x1d0r10 x1d0r11 x1d0m208 x1d0m210 x1d0m218 x1d0m220 : Nat) (hL : L1d0 s S x1d0rcx x1d0rbx x1d0rsi x1d0rdi x1d0r8 x1d0r9 x1d0r10 x1d0r11 x1d0m208 x1d0m210 x1d0m218 x1d0m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1f3)) S (P_1d0_1f3 s y3 x1d0rcx x1d0rbx x1d0rsi x1d0rdi x1d0r8 x1d0r9 x1d0r10 x1d0r11 x1d0m208 x1d0m210 x1d0m218 x1d0m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x1d0rcx, hB_x1d0rcx, hE_x1d0rbx, hB_x1d0rbx, hE_x1d0rsi, hB_x1d0rsi, hE_x1d0rdi, hB_x1d0rdi, hE_x1d0r8, hB_x1d0r8, hE_x1d0r9, hB_x1d0r9, hE_x1d0r10, hB_x1d0r10, hE_x1d0r11, hB_x1d0r11, hE_x1d0m208, hB_x1d0m208, hE_x1d0m210, hB_x1d0m210, hE_x1d0m218, hB_x1d0m218, hE_x1d0m220, hB_x1d0m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x1d0rcx, hE_x1d0rbx, hE_x1d0rsi, hE_x1d0rdi, hE_x1d0r8, hE_x1d0r9, hE_x1d0r10, hE_x1d0r11, hE_x1d0m208, hE_x1d0m210, hE_x1d0m218, hE_x1d0m220, hsp4, Nat.mod_eq_of_lt hB_x1d0rcx, Nat.mod_eq_of_lt hB_x1d0rbx, Nat.mod_eq_of_lt hB_x1d0rsi, Nat.mod_eq_of_lt hB_x1d0rdi, Nat.mod_eq_of_lt hB_x1d0r8, Nat.mod_eq_of_lt hB_x1d0r9, Nat.mod_eq_of_lt hB_x1d0r10, Nat.mod_eq_of_lt hB_x1d0r11, Nat.mod_eq_of_lt hB_x1d0m208, Nat.mod_eq_of_lt hB_x1d0m210, Nat.mod_eq_of_lt hB_x1d0m218, Nat.mod_eq_of_lt hB_x1d0m220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_1d0_1f3
  refine ⟨(if (BitVec.ofNat 64 x1d0rbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r11).toNat, (if (BitVec.ofNat 64 x1d0rbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r10).toNat, ((if (BitVec.ofNat 64 x1d0rbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r11).toNat) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L1f3
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x1d0rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d0rcx)
    · exact hB_x1d0rcx
    · first | exact hE_x1d0rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d0rsi)
    · exact hB_x1d0rsi
    · first | exact hE_x1d0rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d0rdi)
    · exact hB_x1d0rdi
    · first | exact hE_x1d0r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d0r8)
    · exact hB_x1d0r8
    · first | exact hE_x1d0r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d0r9)
    · exact hB_x1d0r9
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d0m208
    · exact hB_x1d0m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d0m210
    · exact hB_x1d0m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d0m218
    · exact hB_x1d0m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d0m220
    · exact hB_x1d0m220
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
