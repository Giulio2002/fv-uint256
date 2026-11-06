import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_290_2b5 (s : State) (x290rax x290rcx x290rdx x290rbx x290rsi x290rdi x290r8 x290r9 x290r10 x290r11 x290r12 x290r13 x290r15 x290m0 x290m8 x290m10 x290m18 x290m60 x290m68 x290m70 x290m78 x290m88 x290m90 x290m98 x290ma0 x290ma8 x290mb0 x290mb8 x290m128 : Nat) (S' : State) : Prop :=
  ∃ x2b5rcx x2b5rbx x2b5r11 x2b5r13 x2b5r15, L2b5 s S' x290rax x2b5rcx x290rdx x2b5rbx x290rsi x290rdi x290r8 x290r9 x290r10 x2b5r11 x2b5r13 x2b5r15 x290m0 x290m8 x290m10 x290m18 x290m60 x290m68 x290m70 x290m88 x290m90 x290m98 x290ma0 x290ma8 x290m128 ∧ x2b5rcx = (x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) % 18446744073709551616 ∧ x2b5rbx = (x290mb0 + x290r15 + (x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x2b5r11 = (x290r11 + x290rcx) % 18446744073709551616 ∧ x2b5r13 = (x290r13 + (x290mb8 + x290r12 + (x290mb0 + x290r15 + (x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x2b5r15 = (x290mb8 + x290r12 + (x290mb0 + x290r15 + (x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_290_2b5 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x290)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x290rax x290rcx x290rdx x290rbx x290rsi x290rdi x290r8 x290r9 x290r10 x290r11 x290r12 x290r13 x290r15 x290m0 x290m8 x290m10 x290m18 x290m60 x290m68 x290m70 x290m78 x290m88 x290m90 x290m98 x290ma0 x290ma8 x290mb0 x290mb8 x290m128 : Nat) (hL : L290 s S x290rax x290rcx x290rdx x290rbx x290rsi x290rdi x290r8 x290r9 x290r10 x290r11 x290r12 x290r13 x290r15 x290m0 x290m8 x290m10 x290m18 x290m60 x290m68 x290m70 x290m78 x290m88 x290m90 x290m98 x290ma0 x290ma8 x290mb0 x290mb8 x290m128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x2b5)) S (P_290_2b5 s  x290rax x290rcx x290rdx x290rbx x290rsi x290rdi x290r8 x290r9 x290r10 x290r11 x290r12 x290r13 x290r15 x290m0 x290m8 x290m10 x290m18 x290m60 x290m68 x290m70 x290m78 x290m88 x290m90 x290m98 x290ma0 x290ma8 x290mb0 x290mb8 x290m128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x290rax, hB_x290rax, hE_x290rcx, hB_x290rcx, hE_x290rdx, hB_x290rdx, hE_x290rbx, hB_x290rbx, hE_x290rsi, hB_x290rsi, hE_x290rdi, hB_x290rdi, hE_x290r8, hB_x290r8, hE_x290r9, hB_x290r9, hE_x290r10, hB_x290r10, hE_x290r11, hB_x290r11, hE_x290r12, hB_x290r12, hE_x290r13, hB_x290r13, hE_x290r15, hB_x290r15, hE_x290m0, hB_x290m0, hE_x290m8, hB_x290m8, hE_x290m10, hB_x290m10, hE_x290m18, hB_x290m18, hE_x290m60, hB_x290m60, hE_x290m68, hB_x290m68, hE_x290m70, hB_x290m70, hE_x290m78, hB_x290m78, hE_x290m88, hB_x290m88, hE_x290m90, hB_x290m90, hE_x290m98, hB_x290m98, hE_x290ma0, hB_x290ma0, hE_x290ma8, hB_x290ma8, hE_x290mb0, hB_x290mb0, hE_x290mb8, hB_x290mb8, hE_x290m128, hB_x290m128⟩ := hL
  janus64_run [Util.readLE_32, hE_x290rax, hE_x290rcx, hE_x290rdx, hE_x290rbx, hE_x290rsi, hE_x290rdi, hE_x290r8, hE_x290r9, hE_x290r10, hE_x290r11, hE_x290r12, hE_x290r13, hE_x290r15, hE_x290m0, hE_x290m8, hE_x290m10, hE_x290m18, hE_x290m60, hE_x290m68, hE_x290m70, hE_x290m78, hE_x290m88, hE_x290m90, hE_x290m98, hE_x290ma0, hE_x290ma8, hE_x290mb0, hE_x290mb8, hE_x290m128, hsp4, Nat.mod_eq_of_lt hB_x290rax, Nat.mod_eq_of_lt hB_x290rcx, Nat.mod_eq_of_lt hB_x290rdx, Nat.mod_eq_of_lt hB_x290rbx, Nat.mod_eq_of_lt hB_x290rsi, Nat.mod_eq_of_lt hB_x290rdi, Nat.mod_eq_of_lt hB_x290r8, Nat.mod_eq_of_lt hB_x290r9, Nat.mod_eq_of_lt hB_x290r10, Nat.mod_eq_of_lt hB_x290r11, Nat.mod_eq_of_lt hB_x290r12, Nat.mod_eq_of_lt hB_x290r13, Nat.mod_eq_of_lt hB_x290r15, Nat.mod_eq_of_lt hB_x290m0, Nat.mod_eq_of_lt hB_x290m8, Nat.mod_eq_of_lt hB_x290m10, Nat.mod_eq_of_lt hB_x290m18, Nat.mod_eq_of_lt hB_x290m60, Nat.mod_eq_of_lt hB_x290m68, Nat.mod_eq_of_lt hB_x290m70, Nat.mod_eq_of_lt hB_x290m78, Nat.mod_eq_of_lt hB_x290m88, Nat.mod_eq_of_lt hB_x290m90, Nat.mod_eq_of_lt hB_x290m98, Nat.mod_eq_of_lt hB_x290ma0, Nat.mod_eq_of_lt hB_x290ma8, Nat.mod_eq_of_lt hB_x290mb0, Nat.mod_eq_of_lt hB_x290mb8, Nat.mod_eq_of_lt hB_x290m128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_290_2b5
  refine ⟨(x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) % 18446744073709551616, (x290mb0 + x290r15 + (x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x290r11 + x290rcx) % 18446744073709551616, (x290r13 + (x290mb8 + x290r12 + (x290mb0 + x290r15 + (x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x290mb8 + x290r12 + (x290mb0 + x290r15 + (x290m78 + x290rbx + (x290r11 + x290rcx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L2b5
    and_intros
    · first | exact hE_x290rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x290rax)
    · exact hB_x290rax
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x290rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x290rdx)
    · exact hB_x290rdx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x290rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x290rsi)
    · exact hB_x290rsi
    · first | exact hE_x290rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x290rdi)
    · exact hB_x290rdi
    · first | exact hE_x290r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x290r8)
    · exact hB_x290r8
    · first | exact hE_x290r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x290r9)
    · exact hB_x290r9
    · first | exact hE_x290r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x290r10)
    · exact hB_x290r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m0
    · exact hB_x290m0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m8
    · exact hB_x290m8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m10
    · exact hB_x290m10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m18
    · exact hB_x290m18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m60
    · exact hB_x290m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m68
    · exact hB_x290m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m70
    · exact hB_x290m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m88
    · exact hB_x290m88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m90
    · exact hB_x290m90
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m98
    · exact hB_x290m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290ma0
    · exact hB_x290ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290ma8
    · exact hB_x290ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x290m128
    · exact hB_x290m128
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
