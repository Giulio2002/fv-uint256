import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.KnuthSub

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub

namespace Fv256.Amd64.KnuthAdd

-- add-back loop of udivremKnuth (head at +0x2a2, exit at +0x2a7)
set_option maxHeartbeats 8000000 in
theorem addback_loop (s0 : State) (up dp n j : Nat) (v cap : W64) (M0 : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20)
    (hua : M0.accessible (up + 8 * j) (8 * n) true = true) (hub : up + 8 * j + 8 * n ≤ 2 ^ 48)
    (hda : M0.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hdu : dp + 8 * n ≤ up + 8 * j ∨ up + 8 * j + 8 * n ≤ dp)
    (hsa : M0.accessible (s0.regs 4).toNat 0x90 true = true)
    (hsu : up + 8 * j + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 0x90 ≤ up + 8 * j)
    (hsd : dp + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 0x90 ≤ dp)
    (hsp : (s0.regs 4).toNat + 0x90 ≤ 2 ^ 48)
    (hsv : M0.readLE ((s0.regs 4).toNat + 0x10) 8 = v.toNat)
    (hscap : M0.readLE ((s0.regs 4).toNat + 0x80) 8 = cap.toNat) :
    ∀ t i c (R : Nat → W64) (fl : Flags) (M : Memory), i + t = n → c ≤ 1 →
      R 10 = BitVec.ofNat 64 n → R 2 = BitVec.ofNat 64 i → R 11 = BitVec.ofNat 64 c →
      R 6 = BitVec.ofNat 64 (up + 8 * j) → R 9 = BitVec.ofNat 64 dp → R 0 = v → R 8 = cap →
      (∀ k, k ∉ [0, 2, 8, 11, 13] → R k = s0.regs k) →
      Fv256.B.wv M0 (up + 8 * j) i + Fv256.B.wv M0 dp i = Fv256.B.wv M (up + 8 * j) i + c * 2 ^ (64 * i) →
      MemFrame M0 M [(up + 8 * j, up + 8 * j + 8 * i)] →
      ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0x2a7))
        { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0x2a2), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (c' : Nat),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x2a7), flags := fl', mem := M' } ∧
          c' ≤ 1 ∧ R' 11 = BitVec.ofNat 64 c' ∧ R' 0 = v ∧ R' 8 = cap ∧ R' 2 = BitVec.ofNat 64 n ∧
          (∀ k, k ∉ [0, 2, 8, 11, 13] → R' k = s0.regs k) ∧
          Fv256.B.wv M0 (up + 8 * j) n + Fv256.B.wv M0 dp n = Fv256.B.wv M' (up + 8 * j) n + c' * 2 ^ (64 * n) ∧
          MemFrame M0 M' [(up + 8 * j, up + 8 * j + 8 * n)]) := by
  intro t
  induction t with
  | zero =>
    intro i c R fl M hi hc e10 e2 e11 e6 e9 e0 e8 hRu hI hfr
    have hin : i = n := by omega
    subst hin
    have hcode := kn_lt
    janus64_run [e10, e2, e11, e6, e9, e0, e8]
    refine ⟨R, _, M, c, rfl, hc, e11, e0, e8, e2, hRu, hI, hfr⟩
  | succ t ih =>
    intro i c R fl M hi hc e10 e2 e11 e6 e9 e0 e8 hRu hI hfr
    have hcode := kn_lt
    have hin : i < n := by omega
    have hMa : M.accessible (up + 8 * j) (8 * n) true = true := by rw [hfr.accessible]; exact hua
    have hMd : M.accessible dp (8 * n) false = true := by rw [hfr.accessible]; exact hda
    have hMs : M.accessible (s0.regs 4).toNat 0x90 true = true := by rw [hfr.accessible]; exact hsa
    have hxi : M.readLE (up + 8 * j + i * 8) 8 = M0.readLE (up + 8 * j + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    have hyi : M.readLE (dp + i * 8) 8 = M0.readLE (dp + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    have hvs : M.readLE ((s0.regs 4).toNat + 0x10) 8 = v.toNat := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hsv
    have hcaps : M.readLE ((s0.regs 4).toNat + 0x80) 8 = cap.toNat := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hscap
    have h4 : R 4 = s0.regs 4 := hRu 4 (by simp)
    have hx1 := Util.readLE8_lt M0 (up + 8 * j + i * 8)
    have hy1 := Util.readLE8_lt M0 (dp + i * 8)
    have hib : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    janus64_run [e10, e2, e11, e6, e9, e0, e8, h4, hxi, hyi, hvs, hcaps, hib] until [kn + 0x2a2]
    have hcz : (!decide (BitVec.setWidth 32 (BitVec.ofNat 64 c) = 0#32)) = decide (c = 1) := by
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · decide
      · decide
    simp only [hcz]
    have hfr' : MemFrame M0 (Janus.Arm64.Memory.writeLE M (up + 8 * j + i * 8) 8
        (addFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8))
          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8)) (decide (c = 1))).fst.toNat)
        [(up + 8 * j, up + 8 * j + 8 * (i + 1))] :=
      (hfr.mono (by intro a m h; simp [Outside] at h ⊢; omega)).writeLE _ (r := (up + 8 * j, up + 8 * j + 8 * (i + 1))) (by simp) (by simp <;> omega) (by simp <;> omega)
    have hcN : (decide (c = 1)).toNat = c := by
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · decide
      · decide
    refine ih (i + 1) ((Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 + Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 + c) / 2 ^ 64) _ _ _
      (by omega) (by omega) e10 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfr'
    · simp [setRegF]
    · simp (config := { decide := true }) only [setRegF, ↓reduceIte, hcN]
      split
      · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
      · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_zero]; omega
    · simp [setRegF, e6]
    · simp [setRegF, e9]
    · simp [setRegF]
    · simp [setRegF]
    · intro k hk
      have hk' : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 8 ∧ k ≠ 11 ∧ k ≠ 13 := by simpa using hk
      obtain ⟨k0, k2, k8, k11, k13⟩ := hk'
      simp [setRegF, k0, k2, k8, k11, k13]
      exact hRu k hk
    · have e1 : Fv256.B.wv M0 (up + 8 * j) (i + 1) = Fv256.B.wv M0 (up + 8 * j) i + 2 ^ (64 * i) * Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have e2 : Fv256.B.wv M0 dp (i + 1) = Fv256.B.wv M0 dp i + 2 ^ (64 * i) * Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have hV : (addFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8))
          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8)) (decide (c = 1))).fst.toNat =
          (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 + Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 + c) % 2 ^ 64 := by
        rw [addFlags_fst]
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hcN]
        have := hx1; have := hy1
        omega
      have e3 : Fv256.B.wv (Janus.Arm64.Memory.writeLE M (up + 8 * j + i * 8) 8
          (addFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8))
            (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8)) (decide (c = 1))).fst.toNat) (up + 8 * j) (i + 1) =
          Fv256.B.wv M (up + 8 * j) i + 2 ^ (64 * i) * ((Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 + Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 + c) % 2 ^ 64) := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8, Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]
        have := Janus.Arm64.Memory.readLE_writeLE_self (m := M) (up + 8 * j + 8 * i) 8
          (addFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8))
            (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8)) (decide (c = 1))).fst.toNat
        rw [Nat.mul_comm i 8] at this hV
        rw [this, hV]
        simp only [Nat.reducePow, Nat.mod_mod]
      rw [e1, e2, e3, show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      simp only [Nat.reducePow] at hI ⊢
      have hdm := Nat.div_add_mod (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 + Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 + c) 18446744073709551616
      generalize 2 ^ (64 * i) = T at *
      generalize (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 + Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 + c) / 18446744073709551616 = q at *
      generalize (Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 + Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 + c) % 18446744073709551616 = r at *
      grind

end Fv256.Amd64.KnuthAdd
