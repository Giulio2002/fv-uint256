import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Arm64.KnuthLem
import Fv256.Arm64.KnuthEst
import Fv256.Arm64.KnuthDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthEst Fv256.Arm64.KnuthDefs
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthIter

set_option maxHeartbeats 8000000 in
/-- The estimate stage of one `udivremKnuth` iteration: from the loop head to the multiply-subtract loop head. -/
theorem est_all (s0 : State) (up dp n m j v dl dh u2 u1 u0 cap : Nat) (hnn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
   (hcap : m ≤ cap) (hcapB : cap < 2 ^ 55)
   (hdh : 2 ^ 63 ≤ dh) (hdh2 : dh < 2 ^ 64) (hdl : dl < 2 ^ 64) (hu2B : u2 < 2 ^ 64) (hu1B : u1 < 2 ^ 64) (hu0B : u0 < 2 ^ 64)
   (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh)
   (hua : s0.mem.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
   (e0 : s0.regs 0 = BitVec.ofNat 64 v) (e2 : s0.regs 2 = BitVec.ofNat 64 dh) (e3 : s0.regs 3 = BitVec.ofNat 64 j)
   (e4 : s0.regs 4 = BitVec.ofNat 64 dl) (e5 : s0.regs 5 = BitVec.ofNat 64 m) (e6 : s0.regs 6 = BitVec.ofNat 64 dp)
   (e7 : s0.regs 7 = BitVec.ofNat 64 cap) (e8 : s0.regs 8 = BitVec.ofNat 64 n) (e9 : s0.regs 9 = BitVec.ofNat 64 up)
   (e10 : s0.regs 10 = BitVec.ofNat 64 (n - 1))
   (hu2 : s0.mem.readLE (up + 8 * (j + n)) 8 = u2) (hu1 : s0.mem.readLE (up + 8 * (j + n - 1)) 8 = u1)
   (hu0 : s0.mem.readLE (up + 8 * (j + n - 2)) 8 = u0)
   (hpc : s0.pc = BitVec.ofNat 64 (kn + 0xbc)) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0x1a8)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags) (qh : Nat),
        S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl' } ∧
        qh = Fv256.B.qhat1 (2 ^ 64) dh dl u2 u1 u0 ∧ qh < 2 ^ 64 ∧
        R' 14 = BitVec.ofNat 64 qh ∧ R' 13 = BitVec.ofNat 64 u2 ∧ R' 11 = 0 ∧ R' 15 = 0 ∧
        R' 12 = BitVec.ofNat 64 (up + 8 * j) ∧ R' 1 = BitVec.ofNat 64 (j + n) ∧
        (∀ k, k ∉ Scratch → R' k = s0.regs k)) := by
  by_cases hlt : u2 < dh
  · have h1 := est_a s0 up dp n m j v dl dh u2 u1 u0 cap hnn hn2 hm hm2 hcap hcapB hua hub e0 e2 e3 e4 e5 e6 e7 e8 e9 e10
      hu2 hu1 hu0 hlt hdh2 hpc
    refine Fv256.B.reachesRet_trans h1 ?_
    intro S1 hrip ⟨R1, fl1, hS1, q11, q12, q13, q1, qu⟩
    subst hS1
    have h2 := est_b { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0xf8), flags := fl1 } dh u2 u1 v hdh hdh2 hlt hu1B hv
      (by show R1 0 = _; exact (qu 0 (by simp)).trans e0) (by show R1 2 = _; exact (qu 2 (by simp)).trans e2) q11 q13 rfl
    refine Fv256.B.reachesRet_trans h2 ?_
    intro S2 hrip2 ⟨R2, fl2, hS2, p14, p11, pu⟩
    subst hS2
    have hQ : (u2 * 2 ^ 64 + u1) / dh < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (u2 + 1) * 2 ^ 64 ≤ dh * 2 ^ 64 := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul] at this
      rw [Nat.mul_comm dh]; omega
    have hrB : (u2 * 2 ^ 64 + u1) % dh < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by omega)) hdh2
    have h3 := est_c { s0 with regs := R2, pc := BitVec.ofNat 64 (kn + 0x130), flags := fl2 } dl _ _ u0 hQ hrB hdl hu0B
      (by show R2 4 = _; exact ((pu 4 (by simp)).trans (qu 4 (by simp))).trans e4) p14 p11
      (by show R2 12 = _; exact (pu 12 (by simp)).trans q12) rfl
    refine Fv256.B.reachesRet_trans h3 ?_
    intro S3 hrip3 ⟨R3, fl3, hS3, r14, ru⟩
    subst hS3
    have h4 := est_d { s0 with regs := R3, pc := BitVec.ofNat 64 (kn + 0x150), flags := fl3 } up n m j cap hnn hn2 hm hm2 hcap hcapB
      (by show R3 3 = _; exact (((ru 3 (by simp)).trans (pu 3 (by simp))).trans (qu 3 (by simp))).trans e3)
      (by show R3 5 = _; exact (((ru 5 (by simp)).trans (pu 5 (by simp))).trans (qu 5 (by simp))).trans e5)
      (by show R3 7 = _; exact (((ru 7 (by simp)).trans (pu 7 (by simp))).trans (qu 7 (by simp))).trans e7)
      (by show R3 9 = _; exact (((ru 9 (by simp)).trans (pu 9 (by simp))).trans (qu 9 (by simp))).trans e9)
      (by show R3 10 = _; exact (((ru 10 (by simp)).trans (pu 10 (by simp))).trans (qu 10 (by simp))).trans e10) rfl
    refine Fv256.B.reachesRet_mono h4 ?_
    intro S4 ⟨R4, fl4, hS4, s11, s15, s12, su⟩
    subst hS4
    have hq : Fv256.B.qhat1 (2 ^ 64) dh dl u2 u1 u0 =
        if ((u2 * 2 ^ 64 + u1) % dh) * 2 ^ 64 + u0 < ((u2 * 2 ^ 64 + u1) / dh) * dl then (u2 * 2 ^ 64 + u1) / dh - 1 else (u2 * 2 ^ 64 + u1) / dh := by
      unfold Fv256.B.qhat1
      rw [if_neg (by omega)]
    refine ⟨R4, fl4, _, rfl, hq.symm, ?_, ?_, ?_, s11, s15, s12, ?_, ?_⟩
    · split <;> omega
    · have := (su 14 (by simp [Scratch])).trans r14
      exact this
    · exact (su 13 (by simp)).trans ((ru 13 (by simp)).trans ((pu 13 (by simp)).trans q13))
    · exact (su 1 (by simp)).trans ((ru 1 (by simp)).trans ((pu 1 (by simp)).trans q1))
    · intro k hk
      have hk' : k ∉ [11, 12, 15] := by simp [Scratch] at hk ⊢; omega
      have hk'' : k ∉ [14, 15, 16] := by simp [Scratch] at hk ⊢; omega
      have hk3 : k ∉ [11, 14, 15, 16] := by simp [Scratch] at hk ⊢; omega
      have hk4 : k ∉ [1, 11, 12, 13] := by simp [Scratch] at hk ⊢; omega
      exact (su k hk').trans ((ru k hk'').trans ((pu k hk3).trans (qu k hk4)))
  · have hge : dh ≤ u2 := by omega
    have h1 := est_ovf s0 up dp n m j v dl dh u2 u1 u0 cap hnn hn2 hm hm2 hcap hcapB hua hub e0 e2 e3 e4 e5 e6 e7 e8 e9 e10
      hu2 hu1 hu0 hge hdh2 hu2B hpc
    refine Fv256.B.reachesRet_trans h1 ?_
    intro S1 hrip ⟨R1, fl1, hS1, q14, q13, q1, qu⟩
    subst hS1
    have h4 := est_d { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x150), flags := fl1 } up n m j cap hnn hn2 hm hm2 hcap hcapB
      (by show R1 3 = _; exact (qu 3 (by simp)).trans e3)
      (by show R1 5 = _; exact (qu 5 (by simp)).trans e5)
      (by show R1 7 = _; exact (qu 7 (by simp)).trans e7)
      (by show R1 9 = _; exact (qu 9 (by simp)).trans e9)
      (by show R1 10 = _; exact (qu 10 (by simp)).trans e10) rfl
    refine Fv256.B.reachesRet_mono h4 ?_
    intro S4 ⟨R4, fl4, hS4, s11, s15, s12, su⟩
    subst hS4
    refine ⟨R4, fl4, 2 ^ 64 - 1, rfl, ?_, by omega, ?_, ?_, s11, s15, s12, ?_, ?_⟩
    · unfold Fv256.B.qhat1
      rw [if_pos hge]
    · exact (su 14 (by simp [Scratch])).trans q14
    · exact (su 13 (by simp)).trans q13
    · exact (su 1 (by simp)).trans q1
    · intro k hk
      have hk' : k ∉ [11, 12, 15] := by simp [Scratch] at hk ⊢; omega
      have hk4 : k ∉ [1, 11, 12, 13, 14] := by simp [Scratch] at hk ⊢; omega
      exact (su k hk').trans (qu k hk4)
end Fv256.Arm64.KnuthIter
