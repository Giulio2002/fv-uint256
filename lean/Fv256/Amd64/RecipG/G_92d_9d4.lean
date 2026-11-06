import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_92d_9d4 (s : State) (y3 : Nat) (x92drcx x92drbx x92drsi x92drdi x92dr8 x92dr9 x92dr10 x92dr11 x92dr12 x92dr13 x92dr15 x92dm40 x92dm48 x92dm50 x92dm60 x92dm68 x92dm70 x92dmc8 x92dmd0 x92dmd8 x92dme0 x92dm100 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x92dm1f8 x92dm200 x92dm208 x92dm210 x92dm218 x92dm220 : Nat) (S' : State) : Prop :=
  ∃ x9d4rax x9d4rdx x9d4mc0 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x9d4m218 x9d4m220, L9d4 s S' x9d4rax x92drcx x9d4rdx x92drbx x92dr10 x92dr11 x92dr12 x92dr13 x92dr15 x92dm40 x92dm48 x92dm50 x92dm60 x92dm68 x92dm70 x9d4mc0 x92dmc8 x92dmd0 x92dmd8 x92dme0 x92dm100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x92dm1f8 x92dm200 x92dm208 x92dm210 x9d4m218 x9d4m220 ∧ x9d4rax = (x92dr9 * x92dm220) % 18446744073709551616 ∧ x9d4rdx = (x92dr9 * x92dm220 / 18446744073709551616) % 18446744073709551616 ∧ x9d4mc0 = (x92drsi * x92dm220 / 18446744073709551616) % 18446744073709551616 ∧ x9d4m160 = (x92drbx * x92dm220) % 18446744073709551616 ∧ x9d4m168 = (x92drbx * x92dm220 / 18446744073709551616) % 18446744073709551616 ∧ x9d4m170 = (x92drsi * x92dm220) % 18446744073709551616 ∧ x9d4m178 = (x92dr8 * x92dm220) % 18446744073709551616 ∧ x9d4m180 = (x92dm220 * x92drdi) % 18446744073709551616 ∧ x9d4m188 = (x92dm220 * x92drdi / 18446744073709551616) % 18446744073709551616 ∧ x9d4m190 = (x92dr9 * x92dm218) % 18446744073709551616 ∧ x9d4m198 = (x92drbx * x92dm218) % 18446744073709551616 ∧ x9d4m1a0 = (x92drbx * x92dm218 / 18446744073709551616) % 18446744073709551616 ∧ x9d4m218 = (x92dr9 * x92dm218 / 18446744073709551616) % 18446744073709551616 ∧ x9d4m220 = (x92dr8 * x92dm220 / 18446744073709551616) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_92d_9d4 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x92d)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x92drcx x92drbx x92drsi x92drdi x92dr8 x92dr9 x92dr10 x92dr11 x92dr12 x92dr13 x92dr15 x92dm40 x92dm48 x92dm50 x92dm60 x92dm68 x92dm70 x92dmc8 x92dmd0 x92dmd8 x92dme0 x92dm100 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x92dm1f8 x92dm200 x92dm208 x92dm210 x92dm218 x92dm220 : Nat) (hL : L92d s S x92drcx x92drbx x92drsi x92drdi x92dr8 x92dr9 x92dr10 x92dr11 x92dr12 x92dr13 x92dr15 x92dm40 x92dm48 x92dm50 x92dm60 x92dm68 x92dm70 x92dmc8 x92dmd0 x92dmd8 x92dme0 x92dm100 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x92dm1f8 x92dm200 x92dm208 x92dm210 x92dm218 x92dm220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x9d4)) S (P_92d_9d4 s y3 x92drcx x92drbx x92drsi x92drdi x92dr8 x92dr9 x92dr10 x92dr11 x92dr12 x92dr13 x92dr15 x92dm40 x92dm48 x92dm50 x92dm60 x92dm68 x92dm70 x92dmc8 x92dmd0 x92dmd8 x92dme0 x92dm100 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x92dm1f8 x92dm200 x92dm208 x92dm210 x92dm218 x92dm220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x92drcx, hB_x92drcx, hE_x92drbx, hB_x92drbx, hE_x92drsi, hB_x92drsi, hE_x92drdi, hB_x92drdi, hE_x92dr8, hB_x92dr8, hE_x92dr9, hB_x92dr9, hE_x92dr10, hB_x92dr10, hE_x92dr11, hB_x92dr11, hE_x92dr12, hB_x92dr12, hE_x92dr13, hB_x92dr13, hE_x92dr15, hB_x92dr15, hE_x92dm40, hB_x92dm40, hE_x92dm48, hB_x92dm48, hE_x92dm50, hB_x92dm50, hE_x92dm60, hB_x92dm60, hE_x92dm68, hB_x92dm68, hE_x92dm70, hB_x92dm70, hE_x92dmc8, hB_x92dmc8, hE_x92dmd0, hB_x92dmd0, hE_x92dmd8, hB_x92dmd8, hE_x92dme0, hB_x92dme0, hE_x92dm100, hB_x92dm100, hE_x92dm1a8, hB_x92dm1a8, hE_x92dm1b0, hB_x92dm1b0, hE_x92dm1b8, hB_x92dm1b8, hE_x92dm1c0, hB_x92dm1c0, hE_x92dm1c8, hB_x92dm1c8, hE_x92dm1d0, hB_x92dm1d0, hE_x92dm1d8, hB_x92dm1d8, hE_x92dm1e0, hB_x92dm1e0, hE_x92dm1e8, hB_x92dm1e8, hE_x92dm1f0, hB_x92dm1f0, hE_x92dm1f8, hB_x92dm1f8, hE_x92dm200, hB_x92dm200, hE_x92dm208, hB_x92dm208, hE_x92dm210, hB_x92dm210, hE_x92dm218, hB_x92dm218, hE_x92dm220, hB_x92dm220⟩ := hL
  janus64_run [Util.readLE_32, hE_x92drcx, hE_x92drbx, hE_x92drsi, hE_x92drdi, hE_x92dr8, hE_x92dr9, hE_x92dr10, hE_x92dr11, hE_x92dr12, hE_x92dr13, hE_x92dr15, hE_x92dm40, hE_x92dm48, hE_x92dm50, hE_x92dm60, hE_x92dm68, hE_x92dm70, hE_x92dmc8, hE_x92dmd0, hE_x92dmd8, hE_x92dme0, hE_x92dm100, hE_x92dm1a8, hE_x92dm1b0, hE_x92dm1b8, hE_x92dm1c0, hE_x92dm1c8, hE_x92dm1d0, hE_x92dm1d8, hE_x92dm1e0, hE_x92dm1e8, hE_x92dm1f0, hE_x92dm1f8, hE_x92dm200, hE_x92dm208, hE_x92dm210, hE_x92dm218, hE_x92dm220, hsp4, Nat.mod_eq_of_lt hB_x92drcx, Nat.mod_eq_of_lt hB_x92drbx, Nat.mod_eq_of_lt hB_x92drsi, Nat.mod_eq_of_lt hB_x92drdi, Nat.mod_eq_of_lt hB_x92dr8, Nat.mod_eq_of_lt hB_x92dr9, Nat.mod_eq_of_lt hB_x92dr10, Nat.mod_eq_of_lt hB_x92dr11, Nat.mod_eq_of_lt hB_x92dr12, Nat.mod_eq_of_lt hB_x92dr13, Nat.mod_eq_of_lt hB_x92dr15, Nat.mod_eq_of_lt hB_x92dm40, Nat.mod_eq_of_lt hB_x92dm48, Nat.mod_eq_of_lt hB_x92dm50, Nat.mod_eq_of_lt hB_x92dm60, Nat.mod_eq_of_lt hB_x92dm68, Nat.mod_eq_of_lt hB_x92dm70, Nat.mod_eq_of_lt hB_x92dmc8, Nat.mod_eq_of_lt hB_x92dmd0, Nat.mod_eq_of_lt hB_x92dmd8, Nat.mod_eq_of_lt hB_x92dme0, Nat.mod_eq_of_lt hB_x92dm100, Nat.mod_eq_of_lt hB_x92dm1a8, Nat.mod_eq_of_lt hB_x92dm1b0, Nat.mod_eq_of_lt hB_x92dm1b8, Nat.mod_eq_of_lt hB_x92dm1c0, Nat.mod_eq_of_lt hB_x92dm1c8, Nat.mod_eq_of_lt hB_x92dm1d0, Nat.mod_eq_of_lt hB_x92dm1d8, Nat.mod_eq_of_lt hB_x92dm1e0, Nat.mod_eq_of_lt hB_x92dm1e8, Nat.mod_eq_of_lt hB_x92dm1f0, Nat.mod_eq_of_lt hB_x92dm1f8, Nat.mod_eq_of_lt hB_x92dm200, Nat.mod_eq_of_lt hB_x92dm208, Nat.mod_eq_of_lt hB_x92dm210, Nat.mod_eq_of_lt hB_x92dm218, Nat.mod_eq_of_lt hB_x92dm220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_92d_9d4
  refine ⟨(x92dr9 * x92dm220) % 18446744073709551616, (x92dr9 * x92dm220 / 18446744073709551616) % 18446744073709551616, (x92drsi * x92dm220 / 18446744073709551616) % 18446744073709551616, (x92drbx * x92dm220) % 18446744073709551616, (x92drbx * x92dm220 / 18446744073709551616) % 18446744073709551616, (x92drsi * x92dm220) % 18446744073709551616, (x92dr8 * x92dm220) % 18446744073709551616, (x92dm220 * x92drdi) % 18446744073709551616, (x92dm220 * x92drdi / 18446744073709551616) % 18446744073709551616, (x92dr9 * x92dm218) % 18446744073709551616, (x92drbx * x92dm218) % 18446744073709551616, (x92drbx * x92dm218 / 18446744073709551616) % 18446744073709551616, (x92dr9 * x92dm218 / 18446744073709551616) % 18446744073709551616, (x92dr8 * x92dm220 / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L9d4
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x92drcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x92drcx)
    · exact hB_x92drcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x92drbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x92drbx)
    · exact hB_x92drbx
    · first | exact hE_x92dr10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x92dr10)
    · exact hB_x92dr10
    · first | exact hE_x92dr11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x92dr11)
    · exact hB_x92dr11
    · first | exact hE_x92dr12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x92dr12)
    · exact hB_x92dr12
    · first | exact hE_x92dr13 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x92dr13)
    · exact hB_x92dr13
    · first | exact hE_x92dr15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x92dr15)
    · exact hB_x92dr15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm40
    · exact hB_x92dm40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm48
    · exact hB_x92dm48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm50
    · exact hB_x92dm50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm60
    · exact hB_x92dm60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm68
    · exact hB_x92dm68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm70
    · exact hB_x92dm70
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dmc8
    · exact hB_x92dmc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dmd0
    · exact hB_x92dmd0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dmd8
    · exact hB_x92dmd8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dme0
    · exact hB_x92dme0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm100
    · exact hB_x92dm100
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1a8
    · exact hB_x92dm1a8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1b0
    · exact hB_x92dm1b0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1b8
    · exact hB_x92dm1b8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1c0
    · exact hB_x92dm1c0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1c8
    · exact hB_x92dm1c8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1d0
    · exact hB_x92dm1d0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1d8
    · exact hB_x92dm1d8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1e0
    · exact hB_x92dm1e0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1e8
    · exact hB_x92dm1e8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1f0
    · exact hB_x92dm1f0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm1f8
    · exact hB_x92dm1f8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm200
    · exact hB_x92dm200
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm208
    · exact hB_x92dm208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x92dm210
    · exact hB_x92dm210
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
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
