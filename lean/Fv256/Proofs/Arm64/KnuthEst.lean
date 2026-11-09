import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.KnuthMathB
import Fv256.Proofs.Arm64.KnuthLem

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthLem
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthEst
abbrev kn : Nat := segAddr Fv256.Arm64.ChainProg.program "github.com/holiman/uint256.udivremKnuth"

set_option maxHeartbeats 8000000 in
theorem est_b (s0 : State) (dh u2 u1 v : Nat) (hdh : 2 ^ 63 ≤ dh) (hdh2 : dh < 2 ^ 64) (hlt : u2 < dh) (hu1 : u1 < 2 ^ 64)
   (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh)
   (e0 : s0.regs 0 = BitVec.ofNat 64 v) (e2 : s0.regs 2 = BitVec.ofNat 64 dh) (e11 : s0.regs 11 = BitVec.ofNat 64 u1)
   (e13 : s0.regs 13 = BitVec.ofNat 64 u2)
   (hpc : s0.pc = BitVec.ofNat 64 (kn + 0xf8)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x130)) s0
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
set_option maxHeartbeats 8000000 in
theorem est_a (s0 : State) (up dp n m j v dl dh u2 u1 u0 cap : Nat) (hnn: 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
   (hcap : m ≤ cap) (hcapB : cap < 2^55)
   (hua : s0.mem.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
   (e0 : s0.regs 0 = BitVec.ofNat 64 v) (e2 : s0.regs 2 = BitVec.ofNat 64 dh) (e3 : s0.regs 3 = BitVec.ofNat 64 j)
   (e4 : s0.regs 4 = BitVec.ofNat 64 dl) (e5 : s0.regs 5 = BitVec.ofNat 64 m) (e6 : s0.regs 6 = BitVec.ofNat 64 dp)
   (e7 : s0.regs 7 = BitVec.ofNat 64 cap) (e8 : s0.regs 8 = BitVec.ofNat 64 n) (e9 : s0.regs 9 = BitVec.ofNat 64 up)
   (e10 : s0.regs 10 = BitVec.ofNat 64 (n - 1))
   (hu2 : s0.mem.readLE (up + 8 * (j + n)) 8 = u2) (hu1 : s0.mem.readLE (up + 8 * (j + n - 1)) 8 = u1) (hu0 : s0.mem.readLE (up + 8 * (j + n - 2)) 8 = u0)
   (hlt : u2 < dh) (hdh2 : dh < 2 ^ 64)
   (hpc : s0.pc = BitVec.ofNat 64 (kn + 0xbc)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0xf8)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags), S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0xf8), flags := fl' } ∧
        R' 11 = BitVec.ofNat 64 u1 ∧ R' 12 = BitVec.ofNat 64 u0 ∧ R' 13 = BitVec.ofNat 64 u2 ∧ R' 1 = BitVec.ofNat 64 (j + n) ∧
        (∀ k, k ∉ [1, 11, 12, 13] → R' k = s0.regs k)) := by
  have hjb : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  have hnsgn : (BitVec.ofNat 64 j).getLsbD 63 = false := by
    rw [BitVec.getLsbD_ofNat]; simp; exact Nat.testBit_lt_two_pow (by omega)
  janus_run [hnsgn, e0, e2, e3, e4, e5, e6, e7, e8, e9, e10, hu2, hu1, hu0, hlt] until [kn + 0xf8]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  · intro k hk
    have hk' : k ≠ 1 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by simpa using hk
    simp [setReg_apply, hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2]
set_option maxHeartbeats 8000000 in
theorem est_ovf (s0 : State) (up dp n m j v dl dh u2 u1 u0 cap : Nat) (hnn: 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
   (hcap : m ≤ cap) (hcapB : cap < 2^55)
   (hua : s0.mem.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
   (e0 : s0.regs 0 = BitVec.ofNat 64 v) (e2 : s0.regs 2 = BitVec.ofNat 64 dh) (e3 : s0.regs 3 = BitVec.ofNat 64 j)
   (e4 : s0.regs 4 = BitVec.ofNat 64 dl) (e5 : s0.regs 5 = BitVec.ofNat 64 m) (e6 : s0.regs 6 = BitVec.ofNat 64 dp)
   (e7 : s0.regs 7 = BitVec.ofNat 64 cap) (e8 : s0.regs 8 = BitVec.ofNat 64 n) (e9 : s0.regs 9 = BitVec.ofNat 64 up)
   (e10 : s0.regs 10 = BitVec.ofNat 64 (n - 1))
   (hu2 : s0.mem.readLE (up + 8 * (j + n)) 8 = u2) (hu1 : s0.mem.readLE (up + 8 * (j + n - 1)) 8 = u1) (hu0 : s0.mem.readLE (up + 8 * (j + n - 2)) 8 = u0)
   (hge : dh ≤ u2) (hdh2 : dh < 2 ^ 64) (hu2B : u2 < 2 ^ 64)
   (hpc : s0.pc = BitVec.ofNat 64 (kn + 0xbc)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x150)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags), S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x150), flags := fl' } ∧
        R' 14 = BitVec.ofNat 64 (2 ^ 64 - 1) ∧ R' 13 = BitVec.ofNat 64 u2 ∧ R' 1 = BitVec.ofNat 64 (j + n) ∧
        (∀ k, k ∉ [1, 11, 12, 13, 14] → R' k = s0.regs k)) := by
  have hjb : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  have hnsgn : (BitVec.ofNat 64 j).getLsbD 63 = false := by
    rw [BitVec.getLsbD_ofNat]; simp; exact Nat.testBit_lt_two_pow (by omega)
  janus_run [hnsgn, e0, e2, e3, e4, e5, e6, e7, e8, e9, e10, hu2, hu1, hu0, hge] until [kn + 0x150]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  · intro k hk
    have hk' : k ≠ 1 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 ∧ k ≠ 14 := by simpa using hk
    simp [setReg_apply, hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, hk'.2.2.2.2]

theorem bv_sub_one (Q : Nat) (h1 : 1 ≤ Q) (hQ : Q < 2 ^ 64) : BitVec.ofNat 64 Q - 1#64 = BitVec.ofNat 64 (Q - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 8000000 in
theorem est_c (s0 : State) (dl Q r u0 : Nat) (hQ : Q < 2 ^ 64) (hr : r < 2 ^ 64) (hdl : dl < 2 ^ 64) (hu0 : u0 < 2 ^ 64)
   (e4 : s0.regs 4 = BitVec.ofNat 64 dl) (e14 : s0.regs 14 = BitVec.ofNat 64 Q) (e11 : s0.regs 11 = BitVec.ofNat 64 r)
   (e12 : s0.regs 12 = BitVec.ofNat 64 u0)
   (hpc : s0.pc = BitVec.ofNat 64 (kn + 0x130)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x150)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags), S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x150), flags := fl' } ∧
        R' 14 = BitVec.ofNat 64 (if r * 2 ^ 64 + u0 < Q * dl then Q - 1 else Q) ∧
        (∀ k, k ∉ [14, 15, 16] → R' k = s0.regs k)) := by
  janus_run [e4, e14, e11, e12] until [kn + 0x150]
  all_goals refine ReachesRet.done (by simp [kn]; rfl) ?_
  all_goals refine ⟨_, _, rfl, ?_, ?_⟩
  all_goals first
    | (intro k hk
       have hk' : k ≠ 14 ∧ k ≠ 15 ∧ k ≠ 16 := by simpa using hk
       simp [setReg_apply, hk'.1, hk'.2.1, hk'.2.2]; done)
    | (simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow] at *
       have e1 : Q % 2 ^ 64 = Q := Nat.mod_eq_of_lt hQ
       have e2 : dl % 2 ^ 64 = dl := Nat.mod_eq_of_lt hdl
       simp only [e1, e2] at *
       generalize hP : Q * dl = P at *
       first
         | (rw [if_pos (by omega)]
            simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
            exact bv_sub_one Q (by rcases Nat.eq_zero_or_pos Q with h | h
                                   · subst h; simp at hP; omega
                                   · exact h) hQ; done)
         | (rw [if_neg (by omega)]
            simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
            exact e14; done))

set_option maxHeartbeats 8000000 in
theorem est_d (s0 : State) (up n m j cap : Nat) (hnn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
   (hcap : m ≤ cap) (hcapB : cap < 2 ^ 55)
   (e3 : s0.regs 3 = BitVec.ofNat 64 j) (e5 : s0.regs 5 = BitVec.ofNat 64 m)
   (e7 : s0.regs 7 = BitVec.ofNat 64 cap) (e9 : s0.regs 9 = BitVec.ofNat 64 up)
   (e10 : s0.regs 10 = BitVec.ofNat 64 (n - 1))
   (hpc : s0.pc = BitVec.ofNat 64 (kn + 0x150)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x1a8)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags), S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl' } ∧
        R' 11 = 0 ∧ R' 15 = 0 ∧ R' 12 = BitVec.ofNat 64 (up + 8 * j) ∧
        (∀ k, k ∉ [11, 12, 15] → R' k = s0.regs k)) := by
  have hsl := slice_ptr_arm j up cap (by omega) hcapB
  janus_run [e3, e5, e7, e9, e10] until [kn + 0x1a8]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setReg_apply]
  · simp [setReg_apply]
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]; exact hsl
  · intro k hk
    have hk' : k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 15 := by simpa using hk
    simp [setReg_apply, hk'.1, hk'.2.1, hk'.2.2]

end Fv256.Arm64.KnuthEst
