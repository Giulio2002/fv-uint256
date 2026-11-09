import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_b9f_bed (s : State) (y3 : Nat) (xb9frcx xb9frdx xb9frbx xb9fm40 xb9fm48 xb9fm50 xb9fm60 : Nat) (S' : State) : Prop :=
  ∃ xbedrdi xbedr8 xbedr10 xbedr12 xbedr15, Lbed s S' xb9frcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 ∧ xbedrdi = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm60 else BitVec.ofNat 64 xb9fm60 - 1#64).toNat ∧ xbedr8 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9frbx else BitVec.ofNat 64 ((xb9frbx % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm60 < 1)).toNat) % 18446744073709551616)).toNat ∧ xbedr10 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm50 else BitVec.ofNat 64 ((xb9fm50 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat) % 18446744073709551616)).toNat ∧ xbedr12 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm48 else BitVec.ofNat 64 ((xb9fm48 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm50 < (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat)).toNat) % 18446744073709551616)).toNat ∧ xbedr15 = (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm40 else BitVec.ofNat 64 ((xb9fm40 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm48 < (decide (xb9fm50 < (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616)).toNat ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_b9f_bed {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xb9f)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xb9frcx xb9frdx xb9frbx xb9fm40 xb9fm48 xb9fm50 xb9fm60 : Nat) (hL : Lb9f s S xb9frcx xb9frdx xb9frbx xb9fm40 xb9fm48 xb9fm50 xb9fm60) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xbed)) S (P_b9f_bed s y3 xb9frcx xb9frdx xb9frbx xb9fm40 xb9fm48 xb9fm50 xb9fm60) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xb9frcx, hB_xb9frcx, hE_xb9frdx, hB_xb9frdx, hE_xb9frbx, hB_xb9frbx, hE_xb9fm40, hB_xb9fm40, hE_xb9fm48, hB_xb9fm48, hE_xb9fm50, hB_xb9fm50, hE_xb9fm60, hB_xb9fm60⟩ := hL
  janus64_run [Util.readLE_32, hE_xb9frcx, hE_xb9frdx, hE_xb9frbx, hE_xb9fm40, hE_xb9fm48, hE_xb9fm50, hE_xb9fm60, hsp4, Nat.mod_eq_of_lt hB_xb9frcx, Nat.mod_eq_of_lt hB_xb9frdx, Nat.mod_eq_of_lt hB_xb9frbx, Nat.mod_eq_of_lt hB_xb9fm40, Nat.mod_eq_of_lt hB_xb9fm48, Nat.mod_eq_of_lt hB_xb9fm50, Nat.mod_eq_of_lt hB_xb9fm60]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_b9f_bed
  refine ⟨(if xb9frdx = 0 then BitVec.ofNat 64 xb9fm60 else BitVec.ofNat 64 xb9fm60 - 1#64).toNat, (if xb9frdx = 0 then BitVec.ofNat 64 xb9frbx else BitVec.ofNat 64 ((xb9frbx % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm60 < 1)).toNat) % 18446744073709551616)).toNat, (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm50 else BitVec.ofNat 64 ((xb9fm50 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat) % 18446744073709551616)).toNat, (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm48 else BitVec.ofNat 64 ((xb9fm48 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm50 < (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat)).toNat) % 18446744073709551616)).toNat, (if xb9frdx = 0 then BitVec.ofNat 64 xb9fm40 else BitVec.ofNat 64 ((xb9fm40 % 18446744073709551616 + 18446744073709551616 - 0 % 18446744073709551616 - (decide (xb9fm48 < (decide (xb9fm50 < (decide (xb9frbx < (decide (xb9fm60 < 1)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616)).toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Lbed
    and_intros
    · first | exact hE_xb9frcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb9frcx)
    · exact hB_xb9frcx
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
