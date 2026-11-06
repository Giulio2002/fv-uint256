import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_bed_c49 (s : State) (y3 : Nat) (xbedrcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 : Nat) (S' : State) : Prop :=
  ∃ xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90, Lc49 s S' xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90 ∧ xc49rcx = (if (BitVec.ofNat 64 xbedrcx).msb = true then 0#64 else BitVec.ofNat 64 xbedrcx).toNat ∧ xc49rdx = (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedrdi + xbedrdi) else BitVec.ofNat 64 xbedrdi).toNat ∧ xc49rbx = (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) else BitVec.ofNat 64 xbedr8).toNat ∧ xc49rsi = (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 xbedr10).toNat ∧ xc49r9 = (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 xbedr12).toNat ∧ xc49r11 = (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr15 + xbedr15 + (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 xbedr15).toNat ∧ xc49m78 = (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) % 18446744073709551616 else xbedr8) % 18446744073709551616 ∧ xc49m80 = (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else xbedr10) % 18446744073709551616 ∧ xc49m88 = (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else xbedr12) % 18446744073709551616 ∧ xc49m90 = (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr15 + xbedr15 + (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else xbedr15) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_bed_c49 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xbed)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xbedrcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 : Nat) (hL : Lbed s S xbedrcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xc49)) S (P_bed_c49 s y3 xbedrcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xbedrcx, hB_xbedrcx, hE_xbedrdi, hB_xbedrdi, hE_xbedr8, hB_xbedr8, hE_xbedr10, hB_xbedr10, hE_xbedr12, hB_xbedr12, hE_xbedr15, hB_xbedr15⟩ := hL
  janus64_run [Util.readLE_32, hE_xbedrcx, hE_xbedrdi, hE_xbedr8, hE_xbedr10, hE_xbedr12, hE_xbedr15, hsp4, Nat.mod_eq_of_lt hB_xbedrcx, Nat.mod_eq_of_lt hB_xbedrdi, Nat.mod_eq_of_lt hB_xbedr8, Nat.mod_eq_of_lt hB_xbedr10, Nat.mod_eq_of_lt hB_xbedr12, Nat.mod_eq_of_lt hB_xbedr15]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_bed_c49
  refine ⟨(if (BitVec.ofNat 64 xbedrcx).msb = true then 0#64 else BitVec.ofNat 64 xbedrcx).toNat, (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedrdi + xbedrdi) else BitVec.ofNat 64 xbedrdi).toNat, (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) else BitVec.ofNat 64 xbedr8).toNat, (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 xbedr10).toNat, (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 xbedr12).toNat, (if (BitVec.ofNat 64 xbedrcx).msb = true then BitVec.ofNat 64 (xbedr15 + xbedr15 + (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) else BitVec.ofNat 64 xbedr15).toNat, (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) % 18446744073709551616 else xbedr8) % 18446744073709551616, (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else xbedr10) % 18446744073709551616, (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else xbedr12) % 18446744073709551616, (if (BitVec.ofNat 64 xbedrcx).msb = true then (xbedr15 + xbedr15 + (xbedr12 + xbedr12 + (xbedr10 + xbedr10 + (xbedr8 + xbedr8 + (xbedrdi + xbedrdi) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 else xbedr15) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Lc49
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
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
