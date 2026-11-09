import Fv256.Proofs.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_2e0_2f8 (s : State) (x2e0rax x2e0rcx x2e0rdx x2e0rbx x2e0rsi x2e0rdi x2e0r8 x2e0r9 x2e0r10 x2e0m0 x2e0m8 x2e0m10 x2e0m18 x2e0m60 x2e0m68 x2e0m70 x2e0m88 x2e0m90 x2e0m128 : Nat) (S' : State) : Prop :=
  ∃ x2f8rax x2f8rcx x2f8rdx x2f8r8 x2f8r10, L2f8 s S' x2f8rax x2f8rcx x2f8rdx x2e0rdi x2f8r8 x2f8r10 x2e0m0 x2e0m8 x2e0m10 x2e0m18 x2e0m60 x2e0m68 x2e0m70 x2e0m88 x2e0m128 ∧ x2f8rax = (x2e0rax + x2e0rsi) % 18446744073709551616 ∧ x2f8rcx = (x2e0m90 + x2e0r9 + (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x2f8rdx = (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) % 18446744073709551616 ∧ x2f8r8 = (x2e0r8 + (x2e0r10 + x2e0rbx + (x2e0m90 + x2e0r9 + (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x2f8r10 = (x2e0r10 + x2e0rbx + (x2e0m90 + x2e0r9 + (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_2e0_2f8 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x2e0)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x2e0rax x2e0rcx x2e0rdx x2e0rbx x2e0rsi x2e0rdi x2e0r8 x2e0r9 x2e0r10 x2e0m0 x2e0m8 x2e0m10 x2e0m18 x2e0m60 x2e0m68 x2e0m70 x2e0m88 x2e0m90 x2e0m128 : Nat) (hL : L2e0 s S x2e0rax x2e0rcx x2e0rdx x2e0rbx x2e0rsi x2e0rdi x2e0r8 x2e0r9 x2e0r10 x2e0m0 x2e0m8 x2e0m10 x2e0m18 x2e0m60 x2e0m68 x2e0m70 x2e0m88 x2e0m90 x2e0m128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x2f8)) S (P_2e0_2f8 s  x2e0rax x2e0rcx x2e0rdx x2e0rbx x2e0rsi x2e0rdi x2e0r8 x2e0r9 x2e0r10 x2e0m0 x2e0m8 x2e0m10 x2e0m18 x2e0m60 x2e0m68 x2e0m70 x2e0m88 x2e0m90 x2e0m128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x2e0rax, hB_x2e0rax, hE_x2e0rcx, hB_x2e0rcx, hE_x2e0rdx, hB_x2e0rdx, hE_x2e0rbx, hB_x2e0rbx, hE_x2e0rsi, hB_x2e0rsi, hE_x2e0rdi, hB_x2e0rdi, hE_x2e0r8, hB_x2e0r8, hE_x2e0r9, hB_x2e0r9, hE_x2e0r10, hB_x2e0r10, hE_x2e0m0, hB_x2e0m0, hE_x2e0m8, hB_x2e0m8, hE_x2e0m10, hB_x2e0m10, hE_x2e0m18, hB_x2e0m18, hE_x2e0m60, hB_x2e0m60, hE_x2e0m68, hB_x2e0m68, hE_x2e0m70, hB_x2e0m70, hE_x2e0m88, hB_x2e0m88, hE_x2e0m90, hB_x2e0m90, hE_x2e0m128, hB_x2e0m128⟩ := hL
  janus64_run [Util.readLE_32, hE_x2e0rax, hE_x2e0rcx, hE_x2e0rdx, hE_x2e0rbx, hE_x2e0rsi, hE_x2e0rdi, hE_x2e0r8, hE_x2e0r9, hE_x2e0r10, hE_x2e0m0, hE_x2e0m8, hE_x2e0m10, hE_x2e0m18, hE_x2e0m60, hE_x2e0m68, hE_x2e0m70, hE_x2e0m88, hE_x2e0m90, hE_x2e0m128, hsp4, Nat.mod_eq_of_lt hB_x2e0rax, Nat.mod_eq_of_lt hB_x2e0rcx, Nat.mod_eq_of_lt hB_x2e0rdx, Nat.mod_eq_of_lt hB_x2e0rbx, Nat.mod_eq_of_lt hB_x2e0rsi, Nat.mod_eq_of_lt hB_x2e0rdi, Nat.mod_eq_of_lt hB_x2e0r8, Nat.mod_eq_of_lt hB_x2e0r9, Nat.mod_eq_of_lt hB_x2e0r10, Nat.mod_eq_of_lt hB_x2e0m0, Nat.mod_eq_of_lt hB_x2e0m8, Nat.mod_eq_of_lt hB_x2e0m10, Nat.mod_eq_of_lt hB_x2e0m18, Nat.mod_eq_of_lt hB_x2e0m60, Nat.mod_eq_of_lt hB_x2e0m68, Nat.mod_eq_of_lt hB_x2e0m70, Nat.mod_eq_of_lt hB_x2e0m88, Nat.mod_eq_of_lt hB_x2e0m90, Nat.mod_eq_of_lt hB_x2e0m128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_2e0_2f8
  refine ⟨(x2e0rax + x2e0rsi) % 18446744073709551616, (x2e0m90 + x2e0r9 + (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) % 18446744073709551616, (x2e0r8 + (x2e0r10 + x2e0rbx + (x2e0m90 + x2e0r9 + (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x2e0r10 + x2e0rbx + (x2e0m90 + x2e0r9 + (x2e0rdx + x2e0rcx + (x2e0rax + x2e0rsi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L2f8
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x2e0rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x2e0rdi)
    · exact hB_x2e0rdi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m0
    · exact hB_x2e0m0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m8
    · exact hB_x2e0m8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m10
    · exact hB_x2e0m10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m18
    · exact hB_x2e0m18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m60
    · exact hB_x2e0m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m68
    · exact hB_x2e0m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m70
    · exact hB_x2e0m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m88
    · exact hB_x2e0m88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2e0m128
    · exact hB_x2e0m128
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold R4Regs
    and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
  · repeat (refine R4Mem.write ?_ _ _ _ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.R4Seg
