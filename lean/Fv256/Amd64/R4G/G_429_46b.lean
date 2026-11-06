import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_429_46b (s : State) (x429rax x429rcx x429rdx x429rbx x429rsi x429rdi x429r8 x429r10 x429r11 x429r12 x429r13 x429m0 x429m8 x429m10 x429m18 x429m30 x429m60 x429m68 x429m88 x429mc8 x429md0 x429md8 x429me0 x429me8 x429mf0 x429m128 : Nat) (S' : State) : Prop :=
  ∃ x46brcx x46br9 x46br11 x46br13, L46b s S' x429rax x46brcx x429rdx x429rbx x429rsi x429rdi x46br9 x46br11 x429r12 x46br13 x429m0 x429m8 x429m10 x429m18 x429m60 x429m68 x429m88 x429mc8 x429m128 ∧ x46brcx = (x429rcx + (x429me8 + x429r10) % 18446744073709551616 + (x429md8 + x429m30) / 18446744073709551616) % 18446744073709551616 ∧ x46br9 = (x429md0 + (x429mf0 + x429r13 + (x429me8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x429rcx + (x429me8 + x429r10) % 18446744073709551616 + (x429md8 + x429m30) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x46br11 = ((x429r11 + x429me0 + (x429mf0 + x429r13 + (x429me8 + x429r10) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x429r8 + (x429md0 + (x429mf0 + x429r13 + (x429me8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x429rcx + (x429me8 + x429r10) % 18446744073709551616 + (x429md8 + x429m30) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x46br13 = (x429md8 + x429m30) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_429_46b (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x429)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x429rax x429rcx x429rdx x429rbx x429rsi x429rdi x429r8 x429r10 x429r11 x429r12 x429r13 x429m0 x429m8 x429m10 x429m18 x429m30 x429m60 x429m68 x429m88 x429mc8 x429md0 x429md8 x429me0 x429me8 x429mf0 x429m128 : Nat) (hL : L429 s S x429rax x429rcx x429rdx x429rbx x429rsi x429rdi x429r8 x429r10 x429r11 x429r12 x429r13 x429m0 x429m8 x429m10 x429m18 x429m30 x429m60 x429m68 x429m88 x429mc8 x429md0 x429md8 x429me0 x429me8 x429mf0 x429m128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x46b)) S (P_429_46b s  x429rax x429rcx x429rdx x429rbx x429rsi x429rdi x429r8 x429r10 x429r11 x429r12 x429r13 x429m0 x429m8 x429m10 x429m18 x429m30 x429m60 x429m68 x429m88 x429mc8 x429md0 x429md8 x429me0 x429me8 x429mf0 x429m128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x429rax, hB_x429rax, hE_x429rcx, hB_x429rcx, hE_x429rdx, hB_x429rdx, hE_x429rbx, hB_x429rbx, hE_x429rsi, hB_x429rsi, hE_x429rdi, hB_x429rdi, hE_x429r8, hB_x429r8, hE_x429r10, hB_x429r10, hE_x429r11, hB_x429r11, hE_x429r12, hB_x429r12, hE_x429r13, hB_x429r13, hE_x429m0, hB_x429m0, hE_x429m8, hB_x429m8, hE_x429m10, hB_x429m10, hE_x429m18, hB_x429m18, hE_x429m30, hB_x429m30, hE_x429m60, hB_x429m60, hE_x429m68, hB_x429m68, hE_x429m88, hB_x429m88, hE_x429mc8, hB_x429mc8, hE_x429md0, hB_x429md0, hE_x429md8, hB_x429md8, hE_x429me0, hB_x429me0, hE_x429me8, hB_x429me8, hE_x429mf0, hB_x429mf0, hE_x429m128, hB_x429m128⟩ := hL
  janus64_run [Util.readLE_32, hE_x429rax, hE_x429rcx, hE_x429rdx, hE_x429rbx, hE_x429rsi, hE_x429rdi, hE_x429r8, hE_x429r10, hE_x429r11, hE_x429r12, hE_x429r13, hE_x429m0, hE_x429m8, hE_x429m10, hE_x429m18, hE_x429m30, hE_x429m60, hE_x429m68, hE_x429m88, hE_x429mc8, hE_x429md0, hE_x429md8, hE_x429me0, hE_x429me8, hE_x429mf0, hE_x429m128, hsp4, Nat.mod_eq_of_lt hB_x429rax, Nat.mod_eq_of_lt hB_x429rcx, Nat.mod_eq_of_lt hB_x429rdx, Nat.mod_eq_of_lt hB_x429rbx, Nat.mod_eq_of_lt hB_x429rsi, Nat.mod_eq_of_lt hB_x429rdi, Nat.mod_eq_of_lt hB_x429r8, Nat.mod_eq_of_lt hB_x429r10, Nat.mod_eq_of_lt hB_x429r11, Nat.mod_eq_of_lt hB_x429r12, Nat.mod_eq_of_lt hB_x429r13, Nat.mod_eq_of_lt hB_x429m0, Nat.mod_eq_of_lt hB_x429m8, Nat.mod_eq_of_lt hB_x429m10, Nat.mod_eq_of_lt hB_x429m18, Nat.mod_eq_of_lt hB_x429m30, Nat.mod_eq_of_lt hB_x429m60, Nat.mod_eq_of_lt hB_x429m68, Nat.mod_eq_of_lt hB_x429m88, Nat.mod_eq_of_lt hB_x429mc8, Nat.mod_eq_of_lt hB_x429md0, Nat.mod_eq_of_lt hB_x429md8, Nat.mod_eq_of_lt hB_x429me0, Nat.mod_eq_of_lt hB_x429me8, Nat.mod_eq_of_lt hB_x429mf0, Nat.mod_eq_of_lt hB_x429m128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_429_46b
  refine ⟨(x429rcx + (x429me8 + x429r10) % 18446744073709551616 + (x429md8 + x429m30) / 18446744073709551616) % 18446744073709551616, (x429md0 + (x429mf0 + x429r13 + (x429me8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x429rcx + (x429me8 + x429r10) % 18446744073709551616 + (x429md8 + x429m30) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ((x429r11 + x429me0 + (x429mf0 + x429r13 + (x429me8 + x429r10) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x429r8 + (x429md0 + (x429mf0 + x429r13 + (x429me8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x429rcx + (x429me8 + x429r10) % 18446744073709551616 + (x429md8 + x429m30) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x429md8 + x429m30) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L46b
    and_intros
    · first | exact hE_x429rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x429rax)
    · exact hB_x429rax
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x429rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x429rdx)
    · exact hB_x429rdx
    · first | exact hE_x429rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x429rbx)
    · exact hB_x429rbx
    · first | exact hE_x429rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x429rsi)
    · exact hB_x429rsi
    · first | exact hE_x429rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x429rdi)
    · exact hB_x429rdi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x429r12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x429r12)
    · exact hB_x429r12
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m0
    · exact hB_x429m0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m8
    · exact hB_x429m8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m10
    · exact hB_x429m10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m18
    · exact hB_x429m18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m60
    · exact hB_x429m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m68
    · exact hB_x429m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m88
    · exact hB_x429m88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429mc8
    · exact hB_x429mc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x429m128
    · exact hB_x429m128
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
