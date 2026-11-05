import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Arm64.KnuthLem

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthLem
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthEst
abbrev kn : Nat := segAddr Extracted.program "github.com/holiman/uint256.udivremKnuth"

set_option maxHeartbeats 8000000 in
theorem est_b (s0 : State) (dh u2 u1 v : Nat) (hdh : 2 ^ 63 ≤ dh) (hdh2 : dh < 2 ^ 64) (hlt : u2 < dh) (hu1 : u1 < 2 ^ 64)
   (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh)
   (e0 : s0.regs 0 = BitVec.ofNat 64 v) (e2 : s0.regs 2 = BitVec.ofNat 64 dh) (e11 : s0.regs 11 = BitVec.ofNat 64 u1)
   (e13 : s0.regs 13 = BitVec.ofNat 64 u2)
   (hpc : s0.pc = BitVec.ofNat 64 (kn + 0xf8)) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0x130)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags), S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x130), flags := fl' } ∧
        R' 14 = BitVec.ofNat 64 ((u2 * 2 ^ 64 + u1) / dh) ∧ R' 11 = BitVec.ofNat 64 ((u2 * 2 ^ 64 + u1) % dh) ∧
        (∀ k, k ∉ [11, 14, 15, 16] → R' k = s0.regs k)) := by
  have hvB : v < 2 ^ 64 := Fv256.B.recip_lt dh v hdh hv
  have hu2B : u2 < 2 ^ 64 := by omega
  have hcorr := Fv256.B.div2by1_correct (2 ^ 64) dh (v + 2 ^ 64) u2 u1 (by omega) hdh2 (by rw [← hv]) hlt hu1
  have hsub : v + 2 ^ 64 - 2 ^ 64 = v := by omega
  rw [hsub] at hcorr
  janus_run [e0, e2, e11, e13] until [kn + 0x130]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · simp only [setReg_apply]
    simp
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, Nat.reducePow, apply_ite BitVec.toNat, qh_val u2 u1 v hu2B hu1 hvB]
    have hQ : (u2 * 2 ^ 64 + u1) / dh < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (u2 + 1) * 2 ^ 64 ≤ dh * 2 ^ 64 := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul] at this
      rw [Nat.mul_comm dh]; omega
    have hdm : dh % 18446744073709551616 = dh := Nat.mod_eq_of_lt hdh2
    have hum : u1 % 18446744073709551616 = u1 := Nat.mod_eq_of_lt hu1
    rw [Nat.mod_eq_of_lt hQ, show (u2 * 2 ^ 64 + u1) / dh = (Fv256.B.div2by1 (2 ^ 64) dh v u2 u1).1 from (congrArg Prod.fst hcorr).symm]
    unfold Fv256.B.div2by1
    simp only [hdm, hum, Nat.reduceMod, Nat.mul_comm u2 v, Nat.reducePow]
    have hPB : v * u2 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hvB hu2B
    have hPB2 : v * u2 / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
    generalize v * u2 = P at *
    simp only [Nat.reducePow] at *
    have hPm : P / 18446744073709551616 % 18446744073709551616 = P / 18446744073709551616 := Nat.mod_eq_of_lt hPB2
    try simp only [hPm]
    have m1 : ∀ x, dh * ((x + 1) % 18446744073709551616) % 18446744073709551616 = dh * (x + 1) % 18446744073709551616 :=
      fun x => Nat.mul_mod_mod _ _ _
    have m2 : ∀ x, (x + 1) % 18446744073709551616 * dh % 18446744073709551616 = dh * (x + 1) % 18446744073709551616 :=
      fun x => by rw [Nat.mod_mul_mod, Nat.mul_comm]
    have m3 : (P + u1) % 18446744073709551616 = (P % 18446744073709551616 + u1) % 18446744073709551616 := by omega
    simp only [m1, m2, m3]
    have hlo := Nat.mod_lt P (show 0 < 18446744073709551616 by decide)
    generalize hc : (P % 18446744073709551616 + u1) / 18446744073709551616 = c
    have hqlt := Nat.mod_lt (P / 18446744073709551616 + u2 + c) (show 0 < 18446744073709551616 by decide)
    generalize hqh : (P / 18446744073709551616 + u2 + c) % 18446744073709551616 = qh at *
    have ht := Nat.mod_lt (dh * (qh + 1)) (show 0 < 18446744073709551616 by decide)
    generalize dh * (qh + 1) % 18446744073709551616 = t at *
    generalize P % 18446744073709551616 = lo at *
    simp only [apply_ite Prod.fst]
    clear hcorr
    repeat' split
    all_goals omega
  · simp only [setReg_apply]
    simp
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, Nat.reducePow, apply_ite BitVec.toNat, qh_val u2 u1 v hu2B hu1 hvB]
    have hQ : (u2 * 2 ^ 64 + u1) % dh < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by omega)) hdh2
    have hQ0 : (u2 * 2 ^ 64 + u1) / dh < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (u2 + 1) * 2 ^ 64 ≤ dh * 2 ^ 64 := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul] at this
      rw [Nat.mul_comm dh]; omega
    have hdm : dh % 18446744073709551616 = dh := Nat.mod_eq_of_lt hdh2
    have hum : u1 % 18446744073709551616 = u1 := Nat.mod_eq_of_lt hu1
    rw [Nat.mod_eq_of_lt hQ, show (u2 * 2 ^ 64 + u1) % dh = (Fv256.B.div2by1 (2 ^ 64) dh v u2 u1).2 from (congrArg Prod.snd hcorr).symm]
    unfold Fv256.B.div2by1
    simp only [hdm, hum, Nat.reduceMod, Nat.mul_comm u2 v, Nat.reducePow]
    have hPB : v * u2 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hvB hu2B
    have hPB2 : v * u2 / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
    generalize v * u2 = P at *
    simp only [Nat.reducePow] at *
    have hPm : P / 18446744073709551616 % 18446744073709551616 = P / 18446744073709551616 := Nat.mod_eq_of_lt hPB2
    try simp only [hPm]
    have m1 : ∀ x, dh * ((x + 1) % 18446744073709551616) % 18446744073709551616 = dh * (x + 1) % 18446744073709551616 :=
      fun x => Nat.mul_mod_mod _ _ _
    have m2 : ∀ x, (x + 1) % 18446744073709551616 * dh % 18446744073709551616 = dh * (x + 1) % 18446744073709551616 :=
      fun x => by rw [Nat.mod_mul_mod, Nat.mul_comm]
    have m3 : (P + u1) % 18446744073709551616 = (P % 18446744073709551616 + u1) % 18446744073709551616 := by omega
    simp only [m1, m2, m3]
    have hlo := Nat.mod_lt P (show 0 < 18446744073709551616 by decide)
    generalize hc : (P % 18446744073709551616 + u1) / 18446744073709551616 = c
    have hqlt := Nat.mod_lt (P / 18446744073709551616 + u2 + c) (show 0 < 18446744073709551616 by decide)
    generalize hqh : (P / 18446744073709551616 + u2 + c) % 18446744073709551616 = qh at *
    have ht := Nat.mod_lt (dh * (qh + 1)) (show 0 < 18446744073709551616 by decide)
    generalize dh * (qh + 1) % 18446744073709551616 = t at *
    generalize P % 18446744073709551616 = lo at *
    simp only [apply_ite Prod.snd]
    clear hcorr
    repeat' split
    all_goals omega
  · intro k hk
    have hk' : k ≠ 11 ∧ k ≠ 14 ∧ k ≠ 15 ∧ k ≠ 16 := by simpa using hk
    simp [setReg_apply, hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2]
end Fv256.Arm64.KnuthEst
