import Fv256.Proofs.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_1f2_20c (s : State) (x1f2rax x1f2rcx x1f2rdx x1f2rsi x1f2rdi x1f2r8 x1f2r9 x1f2r10 x1f2r11 x1f2r13 x1f2r15 x1f2m0 x1f2m8 x1f2m10 x1f2m18 x1f2m40 x1f2m48 x1f2m60 x1f2m68 x1f2m70 x1f2m78 x1f2m80 x1f2m88 x1f2m90 x1f2m98 x1f2ma0 x1f2ma8 x1f2mb0 x1f2mb8 x1f2mc0 x1f2mc8 x1f2md0 x1f2md8 x1f2me0 x1f2me8 x1f2mf0 x1f2mf8 x1f2m100 x1f2m108 x1f2m110 x1f2m128 : Nat) (S' : State) : Prop :=
  ∃ x20crcx x20cr12 x20cr13, L20c s S' x1f2rax x20crcx x1f2rdx x1f2rsi x1f2rdi x1f2r8 x1f2r9 x1f2r10 x1f2r11 x20cr12 x20cr13 x1f2m0 x1f2m8 x1f2m10 x1f2m18 x1f2m40 x1f2m48 x1f2m60 x1f2m68 x1f2m70 x1f2m78 x1f2m80 x1f2m88 x1f2m90 x1f2m98 x1f2ma0 x1f2ma8 x1f2mb0 x1f2mb8 x1f2mc0 x1f2mc8 x1f2md0 x1f2md8 x1f2me0 x1f2me8 x1f2mf0 x1f2mf8 x1f2m100 x1f2m128 ∧ x20crcx = (x1f2m110 + x1f2r15 + (x1f2m108 + x1f2rcx) / 18446744073709551616) % 18446744073709551616 ∧ x20cr12 = (x1f2m108 + x1f2rcx) % 18446744073709551616 ∧ x20cr13 = (x1f2r13 + (x1f2m110 + x1f2r15 + (x1f2m108 + x1f2rcx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_1f2_20c (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x1f2)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x1f2rax x1f2rcx x1f2rdx x1f2rsi x1f2rdi x1f2r8 x1f2r9 x1f2r10 x1f2r11 x1f2r13 x1f2r15 x1f2m0 x1f2m8 x1f2m10 x1f2m18 x1f2m40 x1f2m48 x1f2m60 x1f2m68 x1f2m70 x1f2m78 x1f2m80 x1f2m88 x1f2m90 x1f2m98 x1f2ma0 x1f2ma8 x1f2mb0 x1f2mb8 x1f2mc0 x1f2mc8 x1f2md0 x1f2md8 x1f2me0 x1f2me8 x1f2mf0 x1f2mf8 x1f2m100 x1f2m108 x1f2m110 x1f2m128 : Nat) (hL : L1f2 s S x1f2rax x1f2rcx x1f2rdx x1f2rsi x1f2rdi x1f2r8 x1f2r9 x1f2r10 x1f2r11 x1f2r13 x1f2r15 x1f2m0 x1f2m8 x1f2m10 x1f2m18 x1f2m40 x1f2m48 x1f2m60 x1f2m68 x1f2m70 x1f2m78 x1f2m80 x1f2m88 x1f2m90 x1f2m98 x1f2ma0 x1f2ma8 x1f2mb0 x1f2mb8 x1f2mc0 x1f2mc8 x1f2md0 x1f2md8 x1f2me0 x1f2me8 x1f2mf0 x1f2mf8 x1f2m100 x1f2m108 x1f2m110 x1f2m128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x20c)) S (P_1f2_20c s  x1f2rax x1f2rcx x1f2rdx x1f2rsi x1f2rdi x1f2r8 x1f2r9 x1f2r10 x1f2r11 x1f2r13 x1f2r15 x1f2m0 x1f2m8 x1f2m10 x1f2m18 x1f2m40 x1f2m48 x1f2m60 x1f2m68 x1f2m70 x1f2m78 x1f2m80 x1f2m88 x1f2m90 x1f2m98 x1f2ma0 x1f2ma8 x1f2mb0 x1f2mb8 x1f2mc0 x1f2mc8 x1f2md0 x1f2md8 x1f2me0 x1f2me8 x1f2mf0 x1f2mf8 x1f2m100 x1f2m108 x1f2m110 x1f2m128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x1f2rax, hB_x1f2rax, hE_x1f2rcx, hB_x1f2rcx, hE_x1f2rdx, hB_x1f2rdx, hE_x1f2rsi, hB_x1f2rsi, hE_x1f2rdi, hB_x1f2rdi, hE_x1f2r8, hB_x1f2r8, hE_x1f2r9, hB_x1f2r9, hE_x1f2r10, hB_x1f2r10, hE_x1f2r11, hB_x1f2r11, hE_x1f2r13, hB_x1f2r13, hE_x1f2r15, hB_x1f2r15, hE_x1f2m0, hB_x1f2m0, hE_x1f2m8, hB_x1f2m8, hE_x1f2m10, hB_x1f2m10, hE_x1f2m18, hB_x1f2m18, hE_x1f2m40, hB_x1f2m40, hE_x1f2m48, hB_x1f2m48, hE_x1f2m60, hB_x1f2m60, hE_x1f2m68, hB_x1f2m68, hE_x1f2m70, hB_x1f2m70, hE_x1f2m78, hB_x1f2m78, hE_x1f2m80, hB_x1f2m80, hE_x1f2m88, hB_x1f2m88, hE_x1f2m90, hB_x1f2m90, hE_x1f2m98, hB_x1f2m98, hE_x1f2ma0, hB_x1f2ma0, hE_x1f2ma8, hB_x1f2ma8, hE_x1f2mb0, hB_x1f2mb0, hE_x1f2mb8, hB_x1f2mb8, hE_x1f2mc0, hB_x1f2mc0, hE_x1f2mc8, hB_x1f2mc8, hE_x1f2md0, hB_x1f2md0, hE_x1f2md8, hB_x1f2md8, hE_x1f2me0, hB_x1f2me0, hE_x1f2me8, hB_x1f2me8, hE_x1f2mf0, hB_x1f2mf0, hE_x1f2mf8, hB_x1f2mf8, hE_x1f2m100, hB_x1f2m100, hE_x1f2m108, hB_x1f2m108, hE_x1f2m110, hB_x1f2m110, hE_x1f2m128, hB_x1f2m128⟩ := hL
  janus64_run [Util.readLE_32, hE_x1f2rax, hE_x1f2rcx, hE_x1f2rdx, hE_x1f2rsi, hE_x1f2rdi, hE_x1f2r8, hE_x1f2r9, hE_x1f2r10, hE_x1f2r11, hE_x1f2r13, hE_x1f2r15, hE_x1f2m0, hE_x1f2m8, hE_x1f2m10, hE_x1f2m18, hE_x1f2m40, hE_x1f2m48, hE_x1f2m60, hE_x1f2m68, hE_x1f2m70, hE_x1f2m78, hE_x1f2m80, hE_x1f2m88, hE_x1f2m90, hE_x1f2m98, hE_x1f2ma0, hE_x1f2ma8, hE_x1f2mb0, hE_x1f2mb8, hE_x1f2mc0, hE_x1f2mc8, hE_x1f2md0, hE_x1f2md8, hE_x1f2me0, hE_x1f2me8, hE_x1f2mf0, hE_x1f2mf8, hE_x1f2m100, hE_x1f2m108, hE_x1f2m110, hE_x1f2m128, hsp4, Nat.mod_eq_of_lt hB_x1f2rax, Nat.mod_eq_of_lt hB_x1f2rcx, Nat.mod_eq_of_lt hB_x1f2rdx, Nat.mod_eq_of_lt hB_x1f2rsi, Nat.mod_eq_of_lt hB_x1f2rdi, Nat.mod_eq_of_lt hB_x1f2r8, Nat.mod_eq_of_lt hB_x1f2r9, Nat.mod_eq_of_lt hB_x1f2r10, Nat.mod_eq_of_lt hB_x1f2r11, Nat.mod_eq_of_lt hB_x1f2r13, Nat.mod_eq_of_lt hB_x1f2r15, Nat.mod_eq_of_lt hB_x1f2m0, Nat.mod_eq_of_lt hB_x1f2m8, Nat.mod_eq_of_lt hB_x1f2m10, Nat.mod_eq_of_lt hB_x1f2m18, Nat.mod_eq_of_lt hB_x1f2m40, Nat.mod_eq_of_lt hB_x1f2m48, Nat.mod_eq_of_lt hB_x1f2m60, Nat.mod_eq_of_lt hB_x1f2m68, Nat.mod_eq_of_lt hB_x1f2m70, Nat.mod_eq_of_lt hB_x1f2m78, Nat.mod_eq_of_lt hB_x1f2m80, Nat.mod_eq_of_lt hB_x1f2m88, Nat.mod_eq_of_lt hB_x1f2m90, Nat.mod_eq_of_lt hB_x1f2m98, Nat.mod_eq_of_lt hB_x1f2ma0, Nat.mod_eq_of_lt hB_x1f2ma8, Nat.mod_eq_of_lt hB_x1f2mb0, Nat.mod_eq_of_lt hB_x1f2mb8, Nat.mod_eq_of_lt hB_x1f2mc0, Nat.mod_eq_of_lt hB_x1f2mc8, Nat.mod_eq_of_lt hB_x1f2md0, Nat.mod_eq_of_lt hB_x1f2md8, Nat.mod_eq_of_lt hB_x1f2me0, Nat.mod_eq_of_lt hB_x1f2me8, Nat.mod_eq_of_lt hB_x1f2mf0, Nat.mod_eq_of_lt hB_x1f2mf8, Nat.mod_eq_of_lt hB_x1f2m100, Nat.mod_eq_of_lt hB_x1f2m108, Nat.mod_eq_of_lt hB_x1f2m110, Nat.mod_eq_of_lt hB_x1f2m128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_1f2_20c
  refine ⟨(x1f2m110 + x1f2r15 + (x1f2m108 + x1f2rcx) / 18446744073709551616) % 18446744073709551616, (x1f2m108 + x1f2rcx) % 18446744073709551616, (x1f2r13 + (x1f2m110 + x1f2r15 + (x1f2m108 + x1f2rcx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L20c
    and_intros
    · first | exact hE_x1f2rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2rax)
    · exact hB_x1f2rax
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x1f2rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2rdx)
    · exact hB_x1f2rdx
    · first | exact hE_x1f2rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2rsi)
    · exact hB_x1f2rsi
    · first | exact hE_x1f2rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2rdi)
    · exact hB_x1f2rdi
    · first | exact hE_x1f2r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2r8)
    · exact hB_x1f2r8
    · first | exact hE_x1f2r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2r9)
    · exact hB_x1f2r9
    · first | exact hE_x1f2r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2r10)
    · exact hB_x1f2r10
    · first | exact hE_x1f2r11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1f2r11)
    · exact hB_x1f2r11
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m0
    · exact hB_x1f2m0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m8
    · exact hB_x1f2m8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m10
    · exact hB_x1f2m10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m18
    · exact hB_x1f2m18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m40
    · exact hB_x1f2m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m48
    · exact hB_x1f2m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m60
    · exact hB_x1f2m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m68
    · exact hB_x1f2m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m70
    · exact hB_x1f2m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m78
    · exact hB_x1f2m78
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m80
    · exact hB_x1f2m80
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m88
    · exact hB_x1f2m88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m90
    · exact hB_x1f2m90
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m98
    · exact hB_x1f2m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2ma0
    · exact hB_x1f2ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2ma8
    · exact hB_x1f2ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2mb0
    · exact hB_x1f2mb0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2mb8
    · exact hB_x1f2mb8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2mc0
    · exact hB_x1f2mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2mc8
    · exact hB_x1f2mc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2md0
    · exact hB_x1f2md0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2md8
    · exact hB_x1f2md8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2me0
    · exact hB_x1f2me0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2me8
    · exact hB_x1f2me8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2mf0
    · exact hB_x1f2mf0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2mf8
    · exact hB_x1f2mf8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m100
    · exact hB_x1f2m100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1f2m128
    · exact hB_x1f2m128
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold R4Regs
    and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
  · repeat (refine R4Mem.write ?_ _ _ _ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.R4Seg
