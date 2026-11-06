import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_1d9_1f2 (s : State) (x1d9rax x1d9rdx x1d9rsi x1d9rdi x1d9r8 x1d9r9 x1d9r10 x1d9r11 x1d9r13 x1d9r15 x1d9m0 x1d9m8 x1d9m10 x1d9m18 x1d9m20 x1d9m28 x1d9m40 x1d9m48 x1d9m50 x1d9m60 x1d9m68 x1d9m70 x1d9m78 x1d9m80 x1d9m88 x1d9m90 x1d9m98 x1d9ma0 x1d9ma8 x1d9mb0 x1d9mb8 x1d9mc0 x1d9mc8 x1d9md0 x1d9md8 x1d9me0 x1d9me8 x1d9mf0 x1d9mf8 x1d9m100 x1d9m108 x1d9m110 x1d9m128 : Nat) (S' : State) : Prop :=
  ∃ x1f2rcx x1f2r13 x1f2r15, L1f2 s S' x1d9rax x1f2rcx x1d9rdx x1d9rsi x1d9rdi x1d9r8 x1d9r9 x1d9r10 x1d9r11 x1f2r13 x1f2r15 x1d9m0 x1d9m8 x1d9m10 x1d9m18 x1d9m40 x1d9m48 x1d9m60 x1d9m68 x1d9m70 x1d9m78 x1d9m80 x1d9m88 x1d9m90 x1d9m98 x1d9ma0 x1d9ma8 x1d9mb0 x1d9mb8 x1d9mc0 x1d9mc8 x1d9md0 x1d9md8 x1d9me0 x1d9me8 x1d9mf0 x1d9mf8 x1d9m100 x1d9m108 x1d9m110 x1d9m128 ∧ x1f2rcx = (x1d9m20 + x1d9r15) % 18446744073709551616 ∧ x1f2r13 = (x1d9m50 + (x1d9m28 + x1d9r13 + (x1d9m20 + x1d9r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x1f2r15 = (x1d9m28 + x1d9r13 + (x1d9m20 + x1d9r15) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_1d9_1f2 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x1d9)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x1d9rax x1d9rdx x1d9rsi x1d9rdi x1d9r8 x1d9r9 x1d9r10 x1d9r11 x1d9r13 x1d9r15 x1d9m0 x1d9m8 x1d9m10 x1d9m18 x1d9m20 x1d9m28 x1d9m40 x1d9m48 x1d9m50 x1d9m60 x1d9m68 x1d9m70 x1d9m78 x1d9m80 x1d9m88 x1d9m90 x1d9m98 x1d9ma0 x1d9ma8 x1d9mb0 x1d9mb8 x1d9mc0 x1d9mc8 x1d9md0 x1d9md8 x1d9me0 x1d9me8 x1d9mf0 x1d9mf8 x1d9m100 x1d9m108 x1d9m110 x1d9m128 : Nat) (hL : L1d9 s S x1d9rax x1d9rdx x1d9rsi x1d9rdi x1d9r8 x1d9r9 x1d9r10 x1d9r11 x1d9r13 x1d9r15 x1d9m0 x1d9m8 x1d9m10 x1d9m18 x1d9m20 x1d9m28 x1d9m40 x1d9m48 x1d9m50 x1d9m60 x1d9m68 x1d9m70 x1d9m78 x1d9m80 x1d9m88 x1d9m90 x1d9m98 x1d9ma0 x1d9ma8 x1d9mb0 x1d9mb8 x1d9mc0 x1d9mc8 x1d9md0 x1d9md8 x1d9me0 x1d9me8 x1d9mf0 x1d9mf8 x1d9m100 x1d9m108 x1d9m110 x1d9m128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x1f2)) S (P_1d9_1f2 s  x1d9rax x1d9rdx x1d9rsi x1d9rdi x1d9r8 x1d9r9 x1d9r10 x1d9r11 x1d9r13 x1d9r15 x1d9m0 x1d9m8 x1d9m10 x1d9m18 x1d9m20 x1d9m28 x1d9m40 x1d9m48 x1d9m50 x1d9m60 x1d9m68 x1d9m70 x1d9m78 x1d9m80 x1d9m88 x1d9m90 x1d9m98 x1d9ma0 x1d9ma8 x1d9mb0 x1d9mb8 x1d9mc0 x1d9mc8 x1d9md0 x1d9md8 x1d9me0 x1d9me8 x1d9mf0 x1d9mf8 x1d9m100 x1d9m108 x1d9m110 x1d9m128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x1d9rax, hB_x1d9rax, hE_x1d9rdx, hB_x1d9rdx, hE_x1d9rsi, hB_x1d9rsi, hE_x1d9rdi, hB_x1d9rdi, hE_x1d9r8, hB_x1d9r8, hE_x1d9r9, hB_x1d9r9, hE_x1d9r10, hB_x1d9r10, hE_x1d9r11, hB_x1d9r11, hE_x1d9r13, hB_x1d9r13, hE_x1d9r15, hB_x1d9r15, hE_x1d9m0, hB_x1d9m0, hE_x1d9m8, hB_x1d9m8, hE_x1d9m10, hB_x1d9m10, hE_x1d9m18, hB_x1d9m18, hE_x1d9m20, hB_x1d9m20, hE_x1d9m28, hB_x1d9m28, hE_x1d9m40, hB_x1d9m40, hE_x1d9m48, hB_x1d9m48, hE_x1d9m50, hB_x1d9m50, hE_x1d9m60, hB_x1d9m60, hE_x1d9m68, hB_x1d9m68, hE_x1d9m70, hB_x1d9m70, hE_x1d9m78, hB_x1d9m78, hE_x1d9m80, hB_x1d9m80, hE_x1d9m88, hB_x1d9m88, hE_x1d9m90, hB_x1d9m90, hE_x1d9m98, hB_x1d9m98, hE_x1d9ma0, hB_x1d9ma0, hE_x1d9ma8, hB_x1d9ma8, hE_x1d9mb0, hB_x1d9mb0, hE_x1d9mb8, hB_x1d9mb8, hE_x1d9mc0, hB_x1d9mc0, hE_x1d9mc8, hB_x1d9mc8, hE_x1d9md0, hB_x1d9md0, hE_x1d9md8, hB_x1d9md8, hE_x1d9me0, hB_x1d9me0, hE_x1d9me8, hB_x1d9me8, hE_x1d9mf0, hB_x1d9mf0, hE_x1d9mf8, hB_x1d9mf8, hE_x1d9m100, hB_x1d9m100, hE_x1d9m108, hB_x1d9m108, hE_x1d9m110, hB_x1d9m110, hE_x1d9m128, hB_x1d9m128⟩ := hL
  janus64_run [Util.readLE_32, hE_x1d9rax, hE_x1d9rdx, hE_x1d9rsi, hE_x1d9rdi, hE_x1d9r8, hE_x1d9r9, hE_x1d9r10, hE_x1d9r11, hE_x1d9r13, hE_x1d9r15, hE_x1d9m0, hE_x1d9m8, hE_x1d9m10, hE_x1d9m18, hE_x1d9m20, hE_x1d9m28, hE_x1d9m40, hE_x1d9m48, hE_x1d9m50, hE_x1d9m60, hE_x1d9m68, hE_x1d9m70, hE_x1d9m78, hE_x1d9m80, hE_x1d9m88, hE_x1d9m90, hE_x1d9m98, hE_x1d9ma0, hE_x1d9ma8, hE_x1d9mb0, hE_x1d9mb8, hE_x1d9mc0, hE_x1d9mc8, hE_x1d9md0, hE_x1d9md8, hE_x1d9me0, hE_x1d9me8, hE_x1d9mf0, hE_x1d9mf8, hE_x1d9m100, hE_x1d9m108, hE_x1d9m110, hE_x1d9m128, hsp4, Nat.mod_eq_of_lt hB_x1d9rax, Nat.mod_eq_of_lt hB_x1d9rdx, Nat.mod_eq_of_lt hB_x1d9rsi, Nat.mod_eq_of_lt hB_x1d9rdi, Nat.mod_eq_of_lt hB_x1d9r8, Nat.mod_eq_of_lt hB_x1d9r9, Nat.mod_eq_of_lt hB_x1d9r10, Nat.mod_eq_of_lt hB_x1d9r11, Nat.mod_eq_of_lt hB_x1d9r13, Nat.mod_eq_of_lt hB_x1d9r15, Nat.mod_eq_of_lt hB_x1d9m0, Nat.mod_eq_of_lt hB_x1d9m8, Nat.mod_eq_of_lt hB_x1d9m10, Nat.mod_eq_of_lt hB_x1d9m18, Nat.mod_eq_of_lt hB_x1d9m20, Nat.mod_eq_of_lt hB_x1d9m28, Nat.mod_eq_of_lt hB_x1d9m40, Nat.mod_eq_of_lt hB_x1d9m48, Nat.mod_eq_of_lt hB_x1d9m50, Nat.mod_eq_of_lt hB_x1d9m60, Nat.mod_eq_of_lt hB_x1d9m68, Nat.mod_eq_of_lt hB_x1d9m70, Nat.mod_eq_of_lt hB_x1d9m78, Nat.mod_eq_of_lt hB_x1d9m80, Nat.mod_eq_of_lt hB_x1d9m88, Nat.mod_eq_of_lt hB_x1d9m90, Nat.mod_eq_of_lt hB_x1d9m98, Nat.mod_eq_of_lt hB_x1d9ma0, Nat.mod_eq_of_lt hB_x1d9ma8, Nat.mod_eq_of_lt hB_x1d9mb0, Nat.mod_eq_of_lt hB_x1d9mb8, Nat.mod_eq_of_lt hB_x1d9mc0, Nat.mod_eq_of_lt hB_x1d9mc8, Nat.mod_eq_of_lt hB_x1d9md0, Nat.mod_eq_of_lt hB_x1d9md8, Nat.mod_eq_of_lt hB_x1d9me0, Nat.mod_eq_of_lt hB_x1d9me8, Nat.mod_eq_of_lt hB_x1d9mf0, Nat.mod_eq_of_lt hB_x1d9mf8, Nat.mod_eq_of_lt hB_x1d9m100, Nat.mod_eq_of_lt hB_x1d9m108, Nat.mod_eq_of_lt hB_x1d9m110, Nat.mod_eq_of_lt hB_x1d9m128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_1d9_1f2
  refine ⟨(x1d9m20 + x1d9r15) % 18446744073709551616, (x1d9m50 + (x1d9m28 + x1d9r13 + (x1d9m20 + x1d9r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x1d9m28 + x1d9r13 + (x1d9m20 + x1d9r15) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L1f2
    and_intros
    · first | exact hE_x1d9rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9rax)
    · exact hB_x1d9rax
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x1d9rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9rdx)
    · exact hB_x1d9rdx
    · first | exact hE_x1d9rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9rsi)
    · exact hB_x1d9rsi
    · first | exact hE_x1d9rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9rdi)
    · exact hB_x1d9rdi
    · first | exact hE_x1d9r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9r8)
    · exact hB_x1d9r8
    · first | exact hE_x1d9r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9r9)
    · exact hB_x1d9r9
    · first | exact hE_x1d9r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9r10)
    · exact hB_x1d9r10
    · first | exact hE_x1d9r11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1d9r11)
    · exact hB_x1d9r11
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m0
    · exact hB_x1d9m0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m8
    · exact hB_x1d9m8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m10
    · exact hB_x1d9m10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m18
    · exact hB_x1d9m18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m40
    · exact hB_x1d9m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m48
    · exact hB_x1d9m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m60
    · exact hB_x1d9m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m68
    · exact hB_x1d9m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m70
    · exact hB_x1d9m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m78
    · exact hB_x1d9m78
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m80
    · exact hB_x1d9m80
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m88
    · exact hB_x1d9m88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m90
    · exact hB_x1d9m90
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m98
    · exact hB_x1d9m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9ma0
    · exact hB_x1d9ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9ma8
    · exact hB_x1d9ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9mb0
    · exact hB_x1d9mb0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9mb8
    · exact hB_x1d9mb8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9mc0
    · exact hB_x1d9mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9mc8
    · exact hB_x1d9mc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9md0
    · exact hB_x1d9md0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9md8
    · exact hB_x1d9md8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9me0
    · exact hB_x1d9me0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9me8
    · exact hB_x1d9me8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9mf0
    · exact hB_x1d9mf0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9mf8
    · exact hB_x1d9mf8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m100
    · exact hB_x1d9m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m108
    · exact hB_x1d9m108
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m110
    · exact hB_x1d9m110
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1d9m128
    · exact hB_x1d9m128
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold R4Regs
    and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
  · repeat (refine R4Mem.write ?_ _ _ _ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.R4Seg
