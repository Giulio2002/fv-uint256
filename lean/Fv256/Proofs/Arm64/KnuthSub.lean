import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Arm64.KnuthLem

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthLem
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthSub
abbrev kn : Nat := segAddr Fv256.Arm64.ChainProg.program "github.com/holiman/uint256.udivremKnuth"

set_option maxHeartbeats 8000000 in
/-- multiply-subtract inner loop of `udivremKnuth` (head at +0x1a8, exit at +0x1b0): `x[0..n) -= qh * d[0..n)` with borrow in X15. -/
theorem submul_loop (s0 : State) (ux dp n qh : Nat) (M0 : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hqh : qh < 2 ^ 64)
    (hua : M0.accessible ux (8 * n) true = true) (hub : ux + 8 * n ≤ 2 ^ 48)
    (hda : M0.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hdu : dp + 8 * n ≤ ux ∨ ux + 8 * n ≤ dp) :
    ∀ t i (R : Nat → W64) (fl : Flags) (M : Memory), i + t = n →
      R 8 = BitVec.ofNat 64 n → R 11 = BitVec.ofNat 64 i → R 14 = BitVec.ofNat 64 qh →
      R 12 = BitVec.ofNat 64 ux → R 6 = BitVec.ofNat 64 dp → 
      (∀ k, k ∉ [11, 15, 16, 17, 19, 20, 21] → R k = s0.regs k) →
      Fv256.B.wv M0 ux i + (R 15).toNat * 2 ^ (64 * i) = Fv256.B.wv M ux i + qh * Fv256.B.wv M0 dp i →
      MemFrame M0 M [(ux, ux + 8 * i)] →
      ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x1b0))
        { s0 with regs := R, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x1b0), flags := fl', mem := M' } ∧
          R' 11 = BitVec.ofNat 64 n ∧
          (∀ k, k ∉ [11, 15, 16, 17, 19, 20, 21] → R' k = s0.regs k) ∧
          Fv256.B.wv M0 ux n + (R' 15).toNat * 2 ^ (64 * n) = Fv256.B.wv M' ux n + qh * Fv256.B.wv M0 dp n ∧
          MemFrame M0 M' [(ux, ux + 8 * n)]) := by
  intro t
  induction t with
  | zero =>
    intro i R fl M hi e8 e11 e14 e12 e6 hRu hI hfr
    have hin : i = n := by omega
    subst hin
    simp only [kn, reduceSegAddr, Nat.reduceAdd]
    janus_run [e8, e11]
    refine ⟨R, _, M, rfl, e11, hRu, hI, hfr⟩
  | succ t ih =>
    intro i R fl M hi e8 e11 e14 e12 e6 hRu hI hfr
    have hin : i < n := by omega
    have hMa : M.accessible ux (8 * n) true = true := by rw [hfr.accessible]; exact hua
    have hMd : M.accessible dp (8 * n) false = true := by rw [hfr.accessible]; exact hda
    have hxi : M.readLE (ux + i * 8) 8 = M0.readLE (ux + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    have hyi : M.readLE (dp + i * 8) 8 = M0.readLE (dp + i * 8) 8 := hfr.readLE _ _ (by simp [Outside] <;> omega)
    obtain ⟨b, hbd⟩ : ∃ b, b = (R 15).toNat := ⟨_, rfl⟩
    have hbb : b < 2 ^ 64 := by rw [hbd]; exact (R 15).isLt
    have e15 : R 15 = BitVec.ofNat 64 b := by rw [hbd]; simp
    have hx1 := Util.readLE8_lt M0 (ux + i * 8)
    have hy1 := Util.readLE8_lt M0 (dp + i * 8)
    simp only [kn, reduceSegAddr, Nat.reduceAdd] at ih ⊢
    janus_run [e8, e11, e12, e14, e6, e15, hxi, hyi] until [kn + 0x1a8]
    have hfr' : MemFrame M0 (M.writeLE (ux + i * 8) 8
        (18446744073709551616 - (BitVec.ofNat 64 qh * BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)).toNat +
            (18446744073709551616 - b + M0.readLE (ux + i * 8) 8))) [(ux, ux + 8 * (i + 1))] :=
      (hfr.mono (by intro a m h; simp [Outside] at h ⊢; omega)).writeLE _ (r := (ux, ux + 8 * (i + 1))) (by simp) (by simp <;> omega) (by simp <;> omega)
    refine ih (i + 1) _ _ _ (by omega) e8 ?_ ?_ ?_ ?_ ?_ ?_ hfr'
    · simp [setReg_apply]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    · simp [setReg_apply, e14]
    · simp [setReg_apply, e12]
    · simp [setReg_apply, e6]
    · intro k hk
      have hk' : k ≠ 11 ∧ k ≠ 15 ∧ k ≠ 16 ∧ k ≠ 17 ∧ k ≠ 19 ∧ k ≠ 20 ∧ k ≠ 21 := by simpa using hk
      obtain ⟨k11, k15, k16, k17, k19, k20, k21⟩ := hk'
      simp [setReg_apply, k11, k15, k16, k17, k19, k20, k21]
      exact hRu k hk
    · have key := submul_borrow (M0.readLE (ux + i * 8) 8) (M0.readLE (dp + i * 8) 8) b qh hx1 hy1 hqh hbb
      obtain ⟨hb1, hb2⟩ := Fv256.B.submul_step _ _ qh b hx1 hy1 hqh hbb
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
      rw [key]
      have hV : (18446744073709551616 - (BitVec.ofNat 64 qh * BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)).toNat + (18446744073709551616 - b + (M0.readLE (ux + i * 8) 8))) % 18446744073709551616 =
          (18446744073709551616 - (b + qh * (M0.readLE (dp + i * 8) 8)) % 18446744073709551616 + (M0.readLE (ux + i * 8) 8)) % 18446744073709551616 := by
        simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow]
        have e1 : qh % 18446744073709551616 = qh := Nat.mod_eq_of_lt hqh
        have e2 : (M0.readLE (dp + i * 8) 8) % 18446744073709551616 = (M0.readLE (dp + i * 8) 8) := Nat.mod_eq_of_lt hy1
        rw [e1, e2]
        omega
      have e1 : Fv256.B.wv M0 ux (i + 1) = Fv256.B.wv M0 ux i + 2 ^ (64 * i) * (M0.readLE (ux + i * 8) 8) := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have e2 : Fv256.B.wv M0 dp (i + 1) = Fv256.B.wv M0 dp i + 2 ^ (64 * i) * (M0.readLE (dp + i * 8) 8) := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8]
      have e3 : Fv256.B.wv (M.writeLE (ux + i * 8) 8
          (18446744073709551616 - (BitVec.ofNat 64 qh * BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)).toNat + (18446744073709551616 - b + (M0.readLE (ux + i * 8) 8)))) ux (i + 1) =
          Fv256.B.wv M ux i + 2 ^ (64 * i) * ((18446744073709551616 - (b + qh * (M0.readLE (dp + i * 8) 8)) % 18446744073709551616 + (M0.readLE (ux + i * 8) 8)) % 18446744073709551616) := by
        rw [Fv256.B.wv_snoc, Nat.mul_comm i 8, Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]
        have := Janus.Arm64.Memory.readLE_writeLE_self (m := M) (ux + 8 * i) 8
          (18446744073709551616 - (BitVec.ofNat 64 qh * BitVec.ofNat 64 (M0.readLE (dp + i * 8) 8)).toNat + (18446744073709551616 - b + (M0.readLE (ux + i * 8) 8)))
        rw [Nat.mul_comm i 8] at this
        rw [this]
        simp only [Nat.reducePow]
        simp only [Nat.mul_comm i 8] at hV
        rw [hV]
      rw [e1, e2, e3, show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      simp only [Nat.reducePow] at hb2 hI ⊢
      have := congrArg (· * 2 ^ (64 * i)) hb2
      generalize 2 ^ (64 * i) = T at *
      generalize Fv256.B.wv M0 ux i = W0 at *
      rw [← hbd] at hI
      grind
end Fv256.Arm64.KnuthSub
