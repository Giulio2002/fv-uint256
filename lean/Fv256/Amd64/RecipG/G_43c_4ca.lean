import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_43c_4ca (s : State) (y3 : Nat) (x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 : Nat) (S' : State) : Prop :=
  ∃ x4car9 x4car10 x4car11 x4car12 x4car13 x4car15 x4cam68 x4cam70 x4cam108 x4cam120 x4cam128, L4ca s S' x43crcx x43crsi x4car9 x4car10 x4car11 x4car12 x4car13 x4car15 x4cam68 x4cam70 x43cm98 x43cma0 x43cma8 x4cam108 x4cam120 x4cam128 x43cm208 x43cm210 x43cm218 x43cm220 ∧ x4car9 = (x43crdx * x43crdx / 18446744073709551616) % 18446744073709551616 ∧ x4car10 = (x43crbx * x43crbx / 18446744073709551616) % 18446744073709551616 ∧ x4car11 = (x43crbx * x43cr8) % 18446744073709551616 ∧ x4car12 = (x43crdx * x43cr8 % 18446744073709551616 + x43crdx * x43crbx / 18446744073709551616 + (x43crdx * x43crbx % 18446744073709551616 + x43crbx * x43cr8 / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x4car13 = (x43crdx * x43crbx + x43crbx * x43cr8 / 18446744073709551616) % 18446744073709551616 ∧ x4car15 = (x43crdx * x43cr8 / 18446744073709551616 + (x43crdx * x43cr8 % 18446744073709551616 + x43crdx * x43crbx / 18446744073709551616 + (x43crdx * x43crbx % 18446744073709551616 + x43crbx * x43cr8 / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x4cam68 = (x43crbx * x43crbx % 18446744073709551616 * x43crsi / 18446744073709551616) % 18446744073709551616 ∧ x4cam70 = (x43crbx * x43crbx % 18446744073709551616 * x43crsi) % 18446744073709551616 ∧ x4cam108 = (x43crdx * x43crdx) % 18446744073709551616 ∧ x4cam120 = (x43cr8 * x43cr8) % 18446744073709551616 ∧ x4cam128 = (x43cr8 * x43cr8 / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_43c_4ca {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x43c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 : Nat) (hL : L43c s S x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x4ca)) S (P_43c_4ca s y3 x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x43crcx, hB_x43crcx, hE_x43crdx, hB_x43crdx, hE_x43crbx, hB_x43crbx, hE_x43crsi, hB_x43crsi, hE_x43cr8, hB_x43cr8, hE_x43cm98, hB_x43cm98, hE_x43cma0, hB_x43cma0, hE_x43cma8, hB_x43cma8, hE_x43cm208, hB_x43cm208, hE_x43cm210, hB_x43cm210, hE_x43cm218, hB_x43cm218, hE_x43cm220, hB_x43cm220⟩ := hL
  janus64_run [Util.readLE_32, hE_x43crcx, hE_x43crdx, hE_x43crbx, hE_x43crsi, hE_x43cr8, hE_x43cm98, hE_x43cma0, hE_x43cma8, hE_x43cm208, hE_x43cm210, hE_x43cm218, hE_x43cm220, hsp4, Nat.mod_eq_of_lt hB_x43crcx, Nat.mod_eq_of_lt hB_x43crdx, Nat.mod_eq_of_lt hB_x43crbx, Nat.mod_eq_of_lt hB_x43crsi, Nat.mod_eq_of_lt hB_x43cr8, Nat.mod_eq_of_lt hB_x43cm98, Nat.mod_eq_of_lt hB_x43cma0, Nat.mod_eq_of_lt hB_x43cma8, Nat.mod_eq_of_lt hB_x43cm208, Nat.mod_eq_of_lt hB_x43cm210, Nat.mod_eq_of_lt hB_x43cm218, Nat.mod_eq_of_lt hB_x43cm220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (
  unfold P_43c_4ca
  refine ⟨(x43crdx * x43crdx / 18446744073709551616) % 18446744073709551616, (x43crbx * x43crbx / 18446744073709551616) % 18446744073709551616, (x43crbx * x43cr8) % 18446744073709551616, (x43crdx * x43cr8 % 18446744073709551616 + x43crdx * x43crbx / 18446744073709551616 + (x43crdx * x43crbx % 18446744073709551616 + x43crbx * x43cr8 / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x43crdx * x43crbx + x43crbx * x43cr8 / 18446744073709551616) % 18446744073709551616, (x43crdx * x43cr8 / 18446744073709551616 + (x43crdx * x43cr8 % 18446744073709551616 + x43crdx * x43crbx / 18446744073709551616 + (x43crdx * x43crbx % 18446744073709551616 + x43crbx * x43cr8 / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x43crbx * x43crbx % 18446744073709551616 * x43crsi / 18446744073709551616) % 18446744073709551616, (x43crbx * x43crbx % 18446744073709551616 * x43crsi) % 18446744073709551616, (x43crdx * x43crdx) % 18446744073709551616, (x43cr8 * x43cr8) % 18446744073709551616, (x43cr8 * x43cr8 / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L4ca
    and_intros
    · first | exact hE_x43crcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x43crcx)
    · exact hB_x43crcx
    · first | exact hE_x43crsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x43crsi)
    · exact hB_x43crsi
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
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x43cm98
    · exact hB_x43cm98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x43cma0
    · exact hB_x43cma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x43cma8
    · exact hB_x43cma8
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x43cm208
    · exact hB_x43cm208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x43cm210
    · exact hB_x43cm210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x43cm218
    · exact hB_x43cm218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x43cm220
    · exact hB_x43cm220
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
