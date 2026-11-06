import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_74b_776 (s : State) (y3 : Nat) (x74brax x74brcx x74brdx x74brdi x74br8 x74br9 x74br10 x74br11 x74br12 x74br13 x74br15 x74bm68 x74bm70 x74bm98 x74bma0 x74bma8 x74bm150 x74bm158 x74bm160 x74bm168 x74bm170 x74bm178 x74bm208 x74bm210 x74bm218 x74bm220 : Nat) (S' : State) : Prop :=
  ∃ x776rbx x776rsi x776rdi x776r8 x776r9 x776r10, L776 s S' x74brax x74brcx x776rbx x776rsi x776rdi x776r8 x776r9 x776r10 x74br13 x74bm68 x74bm70 x74bm98 x74bma0 x74bma8 x74bm150 x74bm158 x74bm160 x74bm208 x74bm210 x74bm218 x74bm220 ∧ x776rbx = (x74bm178 + x74br11) % 18446744073709551616 ∧ x776rsi = (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x776rdi = (x74brdi + (x74bm168 + x74brdx + (x74br9 + x74br10 + (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x776r8 = (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) % 18446744073709551616 ∧ x776r9 = (x74br9 + x74br10 + (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x776r10 = (x74bm168 + x74brdx + (x74br9 + x74br10 + (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_74b_776 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x74b)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x74brax x74brcx x74brdx x74brdi x74br8 x74br9 x74br10 x74br11 x74br12 x74br13 x74br15 x74bm68 x74bm70 x74bm98 x74bma0 x74bma8 x74bm150 x74bm158 x74bm160 x74bm168 x74bm170 x74bm178 x74bm208 x74bm210 x74bm218 x74bm220 : Nat) (hL : L74b s S x74brax x74brcx x74brdx x74brdi x74br8 x74br9 x74br10 x74br11 x74br12 x74br13 x74br15 x74bm68 x74bm70 x74bm98 x74bma0 x74bma8 x74bm150 x74bm158 x74bm160 x74bm168 x74bm170 x74bm178 x74bm208 x74bm210 x74bm218 x74bm220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x776)) S (P_74b_776 s y3 x74brax x74brcx x74brdx x74brdi x74br8 x74br9 x74br10 x74br11 x74br12 x74br13 x74br15 x74bm68 x74bm70 x74bm98 x74bma0 x74bma8 x74bm150 x74bm158 x74bm160 x74bm168 x74bm170 x74bm178 x74bm208 x74bm210 x74bm218 x74bm220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x74brax, hB_x74brax, hE_x74brcx, hB_x74brcx, hE_x74brdx, hB_x74brdx, hE_x74brdi, hB_x74brdi, hE_x74br8, hB_x74br8, hE_x74br9, hB_x74br9, hE_x74br10, hB_x74br10, hE_x74br11, hB_x74br11, hE_x74br12, hB_x74br12, hE_x74br13, hB_x74br13, hE_x74br15, hB_x74br15, hE_x74bm68, hB_x74bm68, hE_x74bm70, hB_x74bm70, hE_x74bm98, hB_x74bm98, hE_x74bma0, hB_x74bma0, hE_x74bma8, hB_x74bma8, hE_x74bm150, hB_x74bm150, hE_x74bm158, hB_x74bm158, hE_x74bm160, hB_x74bm160, hE_x74bm168, hB_x74bm168, hE_x74bm170, hB_x74bm170, hE_x74bm178, hB_x74bm178, hE_x74bm208, hB_x74bm208, hE_x74bm210, hB_x74bm210, hE_x74bm218, hB_x74bm218, hE_x74bm220, hB_x74bm220⟩ := hL
  janus64_run [Util.readLE_32, hE_x74brax, hE_x74brcx, hE_x74brdx, hE_x74brdi, hE_x74br8, hE_x74br9, hE_x74br10, hE_x74br11, hE_x74br12, hE_x74br13, hE_x74br15, hE_x74bm68, hE_x74bm70, hE_x74bm98, hE_x74bma0, hE_x74bma8, hE_x74bm150, hE_x74bm158, hE_x74bm160, hE_x74bm168, hE_x74bm170, hE_x74bm178, hE_x74bm208, hE_x74bm210, hE_x74bm218, hE_x74bm220, hsp4, Nat.mod_eq_of_lt hB_x74brax, Nat.mod_eq_of_lt hB_x74brcx, Nat.mod_eq_of_lt hB_x74brdx, Nat.mod_eq_of_lt hB_x74brdi, Nat.mod_eq_of_lt hB_x74br8, Nat.mod_eq_of_lt hB_x74br9, Nat.mod_eq_of_lt hB_x74br10, Nat.mod_eq_of_lt hB_x74br11, Nat.mod_eq_of_lt hB_x74br12, Nat.mod_eq_of_lt hB_x74br13, Nat.mod_eq_of_lt hB_x74br15, Nat.mod_eq_of_lt hB_x74bm68, Nat.mod_eq_of_lt hB_x74bm70, Nat.mod_eq_of_lt hB_x74bm98, Nat.mod_eq_of_lt hB_x74bma0, Nat.mod_eq_of_lt hB_x74bma8, Nat.mod_eq_of_lt hB_x74bm150, Nat.mod_eq_of_lt hB_x74bm158, Nat.mod_eq_of_lt hB_x74bm160, Nat.mod_eq_of_lt hB_x74bm168, Nat.mod_eq_of_lt hB_x74bm170, Nat.mod_eq_of_lt hB_x74bm178, Nat.mod_eq_of_lt hB_x74bm208, Nat.mod_eq_of_lt hB_x74bm210, Nat.mod_eq_of_lt hB_x74bm218, Nat.mod_eq_of_lt hB_x74bm220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_74b_776
  refine ⟨(x74bm178 + x74br11) % 18446744073709551616, (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x74brdi + (x74bm168 + x74brdx + (x74br9 + x74br10 + (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) % 18446744073709551616, (x74br9 + x74br10 + (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x74bm168 + x74brdx + (x74br9 + x74br10 + (x74bm170 + x74br15 + (x74br8 + x74br12 + (x74bm178 + x74br11) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L776
    and_intros
    · first | exact hE_x74brax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x74brax)
    · exact hB_x74brax
    · first | exact hE_x74brcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x74brcx)
    · exact hB_x74brcx
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
    · first | exact hE_x74br13 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x74br13)
    · exact hB_x74br13
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm68
    · exact hB_x74bm68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm70
    · exact hB_x74bm70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm98
    · exact hB_x74bm98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bma0
    · exact hB_x74bma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bma8
    · exact hB_x74bma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm150
    · exact hB_x74bm150
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm158
    · exact hB_x74bm158
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm160
    · exact hB_x74bm160
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm208
    · exact hB_x74bm208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm210
    · exact hB_x74bm210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm218
    · exact hB_x74bm218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x74bm220
    · exact hB_x74bm220
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
