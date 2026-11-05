import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Arm64.KnuthLem

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthLem
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthAdd
abbrev kn : Nat := segAddr Extracted.program "github.com/holiman/uint256.udivremKnuth"

set_option maxHeartbeats 8000000 in
/-- add-back loop of `udivremKnuth` (head at +0x210, exit at +0x218): `x[0..n) += d[0..n)` with carry in X13. -/
theorem addback_loop (s0 : State) (ux dp n : Nat) (M0 : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20)
    (hua : M0.accessible ux (8 * n) true = true) (hub : ux + 8 * n ≤ 2 ^ 48)
    (hda : M0.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hdu : dp + 8 * n ≤ ux ∨ ux + 8 * n ≤ dp) :
    ∀ t i c (R : Nat → W64) (fl : Flags) (M : Memory), i + t = n → c ≤ 1 →
      R 8 = BitVec.ofNat 64 n → R 11 = BitVec.ofNat 64 i → R 13 = BitVec.ofNat 64 c →
      R 12 = BitVec.ofNat 64 ux → R 6 = BitVec.ofNat 64 dp →
      (∀ k, k ∉ [11, 13, 15, 16, 17, 19, 20] → R k = s0.regs k) →
      Fv256.B.wv M0 ux i + Fv256.B.wv M0 dp i = Fv256.B.wv M ux i + c * 2 ^ (64 * i) →
      MemFrame M0 M [(ux, ux + 8 * i)] →
      ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0x218))
        { s0 with regs := R, pc := BitVec.ofNat 64 (kn + 0x210), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (c' : Nat),
          S' = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x218), flags := fl', mem := M' } ∧
          c' ≤ 1 ∧ R' 13 = BitVec.ofNat 64 c' ∧
          (∀ k, k ∉ [11, 13, 15, 16, 17, 19, 20] → R' k = s0.regs k) ∧
          Fv256.B.wv M0 ux n + Fv256.B.wv M0 dp n = Fv256.B.wv M' ux n + c' * 2 ^ (64 * n) ∧
          MemFrame M0 M' [(ux, ux + 8 * n)]) := by
  intro t
  induction t with
  | zero =>
    intro i c R fl M hi hc e8 e11 e13 e12 e6 hRu hI hfr
    have hin : i = n := by omega
    subst hin
    simp only [kn, reduceSegAddr, Nat.reduceAdd]
    janus_run [e8, e11]
    refine ⟨R, _, M, c, rfl, hc, e13, hRu, hI, hfr⟩
  | succ t ih =>
    intro i c R fl M hi hc e8 e11 e13 e12 e6 hRu hI hfr
    have hin : i < n := by omega
    have hMa : M.accessible ux (8 * n) true = true := by rw [hfr.accessible]; exact hua
    have hMd : M.accessible dp (8 * n) false = true := by rw [hfr.accessible]; exact hda
    have hxi : M.readLE (ux + i * 8) 8 = M0.readLE (ux + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    have hyi : M.readLE (dp + i * 8) 8 = M0.readLE (dp + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    have hx1 := Util.readLE8_lt M0 (ux + i * 8)
    have hy1 := Util.readLE8_lt M0 (dp + i * 8)
    simp only [kn, reduceSegAddr, Nat.reduceAdd] at ih ⊢
    janus_run [e8, e11, e12, e13, e6, hxi, hyi] until [kn + 0x210]
    have hcar : (addWithCarry (BitVec.ofNat 64 c) (18446744073709551615#64) false).snd.c = decide (c = 1) := by
      rw [awc_c]
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · decide
      · decide
    have hcN : (decide (c = 1)).toNat = c := by
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · decide
      · decide
    simp only [hcar]
    have hV : (addWithCarry (BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)) (BitVec.ofNat 64 (M0.readLE (ux + i * 8) 8)) (decide (c = 1))).fst.toNat =
        (M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) % 2 ^ 64 := by
      rw [awc_fst]
      simp only [BitVec.toNat_ofNat, hcN]
      rw [Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1]
    have hC : (addWithCarry (BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)) (BitVec.ofNat 64 (M0.readLE (ux + i * 8) 8)) (decide (c = 1))).snd.c =
        decide (2 ^ 64 ≤ M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) := by
      rw [awc_c]
      simp only [BitVec.toNat_ofNat, hcN]
      rw [Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1]
    have hfr' : MemFrame M0 (M.writeLE (ux + i * 8) 8
        (addWithCarry (BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)) (BitVec.ofNat 64 (M0.readLE (ux + i * 8) 8)) (decide (c = 1))).fst.toNat)
        [(ux, ux + 8 * (i + 1))] :=
      (hfr.mono (by intro a m h; simp [Outside] at h ⊢; omega)).writeLE _ (r := (ux, ux + 8 * (i + 1))) (by simp) (by simp <;> omega) (by simp <;> omega)
    have hcn : ((M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) / 2 ^ 64) ≤ 1 := by omega
    have hdN : (decide (2 ^ 64 ≤ M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c)).toNat = (M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) / 2 ^ 64 := by
      by_cases h : 2 ^ 64 ≤ M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c
      · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega
      · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega
    refine ih (i + 1) ((M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) / 2 ^ 64) _ _ _ (by omega) hcn e8 ?_ ?_ ?_ ?_ ?_ ?_ hfr'
    · simp [setReg_apply]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte, hC]
      apply BitVec.eq_of_toNat_eq
      rw [awc_fst]
      simp only [BitVec.toNat_ofNat, hdN, Nat.zero_add]
      have : (M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) / 2 ^ 64 < 2 ^ 64 := by omega
      omega
    · simp [setReg_apply, e12]
    · simp [setReg_apply, e6]
    · intro k hk
      have hk' : k ≠ 11 ∧ k ≠ 13 ∧ k ≠ 15 ∧ k ≠ 16 ∧ k ≠ 17 ∧ k ≠ 19 ∧ k ≠ 20 := by simpa using hk
      obtain ⟨k11, k13, k15, k16, k17, k19, k20⟩ := hk'
      simp [setReg_apply, k11, k13, k15, k16, k17, k19, k20]
      exact hRu k hk
    · have e1 : Fv256.B.wv M0 ux (i + 1) = Fv256.B.wv M0 ux i + 2 ^ (64 * i) * M0.readLE (ux + i * 8) 8 := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have e2 : Fv256.B.wv M0 dp (i + 1) = Fv256.B.wv M0 dp i + 2 ^ (64 * i) * M0.readLE (dp + i * 8) 8 := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have e3 : Fv256.B.wv (M.writeLE (ux + i * 8) 8
          (addWithCarry (BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)) (BitVec.ofNat 64 (M0.readLE (ux + i * 8) 8)) (decide (c = 1))).fst.toNat)
            ux (i + 1) =
          Fv256.B.wv M ux i + 2 ^ (64 * i) * ((M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) % 2 ^ 64) := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8, Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]
        have := Janus.Arm64.Memory.readLE_writeLE_self (m := M) (ux + 8 * i) 8
          (addWithCarry (BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)) (BitVec.ofNat 64 (M0.readLE (ux + i * 8) 8)) (decide (c = 1))).fst.toNat
        simp only [Nat.mul_comm i 8] at hV this ⊢
        rw [this, hV]
        simp only [Nat.reducePow, Nat.mod_mod]
      rw [e1, e2, e3, show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      simp only [Nat.reducePow] at hI ⊢
      have hdm := Nat.div_add_mod (M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) 18446744073709551616
      generalize 2 ^ (64 * i) = T at *
      generalize (M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) / 18446744073709551616 = q at *
      generalize (M0.readLE (dp + i * 8) 8 + M0.readLE (ux + i * 8) 8 + c) % 18446744073709551616 = r at *
      grind
end Fv256.Arm64.KnuthAdd
