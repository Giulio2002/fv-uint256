import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.KnuthSub

abbrev kn : Nat := segAddr Fv256.ChainProg.program "github.com/holiman/uint256.udivremKnuth"

theorem kn_lt : kn + 0x2c0 < 2 ^ 47 := by decide

-- multiply-subtract inner loop of udivremKnuth (head at +0x235, exit at +0x23a)
set_option maxHeartbeats 8000000 in
theorem submul_loop (s0 : State) (up dp n j qh : Nat) (v c u2 cap : W64) (M0 : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hqh : qh < 2 ^ 64)
    (hua : M0.accessible (up + 8 * j) (8 * n) true = true) (hub : up + 8 * j + 8 * n ≤ 2 ^ 48)
    (hda : M0.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hdu : dp + 8 * n ≤ up + 8 * j ∨ up + 8 * j + 8 * n ≤ dp)
    (hsa : M0.accessible (s0.regs 4).toNat 0x90 true = true)
    (hsu : up + 8 * j + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 0x90 ≤ up + 8 * j)
    (hsd : dp + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 0x90 ≤ dp)
    (hsp : (s0.regs 4).toNat + 0x90 ≤ 2 ^ 48)
    (hsv : M0.readLE ((s0.regs 4).toNat + 0x10) 8 = v.toNat) (hsc : M0.readLE ((s0.regs 4).toNat + 0x40) 8 = c.toNat)
    (hsu2 : M0.readLE (s0.regs 4).toNat 8 = u2.toNat) (hscap : M0.readLE ((s0.regs 4).toNat + 0x80) 8 = cap.toNat) :
    ∀ t i (R : Nat → W64) (fl : Flags) (M : Memory), i + t = n →
      R 10 = BitVec.ofNat 64 n → R 11 = BitVec.ofNat 64 i → R 3 = BitVec.ofNat 64 qh →
      R 6 = BitVec.ofNat 64 (up + 8 * j) → R 9 = BitVec.ofNat 64 dp → R 0 = v → R 1 = c → R 2 = u2 → R 8 = cap →
      (∀ k, k ∉ [0, 1, 2, 8, 11, 13] → R k = s0.regs k) →
      Fv256.B.wv M0 (up + 8 * j) i + (R 13).toNat * 2 ^ (64 * i) = Fv256.B.wv M (up + 8 * j) i + qh * Fv256.B.wv M0 dp i →
      MemFrame M0 M [(up + 8 * j, up + 8 * j + 8 * i)] →
      ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0x23a))
        { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0x235), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x23a), flags := fl', mem := M' } ∧
          R' 11 = BitVec.ofNat 64 n ∧ R' 0 = v ∧ R' 1 = c ∧ R' 2 = u2 ∧ R' 8 = cap ∧
          (∀ k, k ∉ [0, 1, 2, 8, 11, 13] → R' k = s0.regs k) ∧
          Fv256.B.wv M0 (up + 8 * j) n + (R' 13).toNat * 2 ^ (64 * n) = Fv256.B.wv M' (up + 8 * j) n + qh * Fv256.B.wv M0 dp n ∧
          MemFrame M0 M' [(up + 8 * j, up + 8 * j + 8 * n)]) := by
  intro t
  induction t with
  | zero =>
    intro i R fl M hi e10 e11 e3 e6 e9 e0 e1 e2 e8 hRu hI hfr
    have hin : i = n := by omega
    subst hin
    have hcode := kn_lt
    janus64_run [e10, e11, e3, e6, e9, e0, e1, e2, e8]
    refine ⟨R, _, M, rfl, e11, e0, e1, e2, e8, hRu, hI, hfr⟩
  | succ t ih =>
    intro i R fl M hi e10 e11 e3 e6 e9 e0 e1 e2 e8 hRu hI hfr
    have hcode := kn_lt
    have hin : i < n := by omega
    have hMa : M.accessible (up + 8 * j) (8 * n) true = true := by rw [hfr.accessible]; exact hua
    have hMd : M.accessible dp (8 * n) false = true := by rw [hfr.accessible]; exact hda
    have hMs : M.accessible (s0.regs 4).toNat 0x90 true = true := by rw [hfr.accessible]; exact hsa
    have hxi : M.readLE (up + 8 * j + i * 8) 8 = M0.readLE (up + 8 * j + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    have hyi : M.readLE (dp + i * 8) 8 = M0.readLE (dp + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    have hvs : M.readLE ((s0.regs 4).toNat + 0x10) 8 = v.toNat := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hsv
    have hcs : M.readLE ((s0.regs 4).toNat + 0x40) 8 = c.toNat := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hsc
    have hus2 : M.readLE (s0.regs 4).toNat 8 = u2.toNat := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hsu2
    have hcaps : M.readLE ((s0.regs 4).toNat + 0x80) 8 = cap.toNat := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hscap
    have h4 : R 4 = s0.regs 4 := hRu 4 (by simp)
    have h7 : R 7 = s0.regs 7 := hRu 7 (by simp)
    obtain ⟨b, hbd⟩ : ∃ b, b = (R 13).toNat := ⟨_, rfl⟩
    have hbb : b < 2 ^ 64 := by rw [hbd]; exact (R 13).isLt
    have e13 : R 13 = BitVec.ofNat 64 b := by rw [hbd]; simp
    have hx1 := Util.readLE8_lt M0 (up + 8 * j + i * 8)
    have hy1 := Util.readLE8_lt M0 (dp + i * 8)
    janus64_run [e10, e11, e13, e3, e6, e9, e0, e1, e2, e8, h4, h7, hxi, hyi, hvs, hcs, hus2, hcaps] until [kn + 0x235]
    obtain ⟨hb1, hb2⟩ := Fv256.B.submul_step _ _ qh b hx1 hy1 hqh hbb
    have hfr' : MemFrame M0 (Janus.Arm64.Memory.writeLE M (up + 8 * j + i * 8) 8
        (18446744073709551616 - (b + qh * Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8) % 18446744073709551616 +
          Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8)) [(up + 8 * j, up + 8 * j + 8 * (i + 1))] :=
      (hfr.mono (by intro a m h; simp [Outside] at h ⊢; omega)).writeLE _ (r := (up + 8 * j, up + 8 * j + 8 * (i + 1))) (by simp) (by simp <;> omega) (by simp <;> omega)
    refine ih (i + 1) _ _ _ (by omega) e10 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfr'
    · simp [setRegF]
    · simp [setRegF, e3]
    · simp [setRegF, e6]
    · simp [setRegF, e9]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · intro k hk
      have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 8 ∧ k ≠ 11 ∧ k ≠ 13 := by simpa using hk
      obtain ⟨k0, k1, k2, k8, k11, k13⟩ := hk'
      simp [setRegF, k0, k1, k2, k8, k11, k13]
      exact hRu k hk
    · simp only [setRegF, if_true]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using hb1)]
      have e1 : Fv256.B.wv M0 (up + 8 * j) (i + 1) = Fv256.B.wv M0 (up + 8 * j) i + 2 ^ (64 * i) * Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8 := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have e2 : Fv256.B.wv M0 dp (i + 1) = Fv256.B.wv M0 dp i + 2 ^ (64 * i) * Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8 := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have e3' : Fv256.B.wv (Janus.Arm64.Memory.writeLE M (up + 8 * j + i * 8) 8
          (18446744073709551616 - (b + qh * Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8) % 18446744073709551616 +
            Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8)) (up + 8 * j) (i + 1) =
          Fv256.B.wv M (up + 8 * j) i + 2 ^ (64 * i) * ((18446744073709551616 - (b + qh * Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8) % 18446744073709551616 +
            Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8) % 18446744073709551616) := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8, Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]
        have := Janus.Arm64.Memory.readLE_writeLE_self (m := M) (up + 8 * j + 8 * i) 8
          (18446744073709551616 - (b + qh * Janus.Arm64.Memory.readLE M0 (dp + i * 8) 8) % 18446744073709551616 +
            Janus.Arm64.Memory.readLE M0 (up + 8 * j + i * 8) 8)
        rw [Nat.mul_comm i 8] at this
        rw [this]
      rw [e1, e2, e3', show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      simp only [Nat.reducePow] at hb2 ⊢
      have := congrArg (· * 2 ^ (64 * i)) hb2
      generalize 2 ^ (64 * i) = T at *
      generalize Fv256.B.wv M0 (up + 8 * j) i = W0 at *
      rw [← hbd] at hI
      grind

end Fv256.Amd64.KnuthSub
