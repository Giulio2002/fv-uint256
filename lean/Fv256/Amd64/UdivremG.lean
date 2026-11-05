import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.UdivMathB
import Fv256.Amd64.UdivremA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA

namespace Fv256.Amd64.UdivremG

-- from the `dLen` loop exit (+0x4c) to the head of the divisor normalisation loop (+0x140)
set_option maxHeartbeats 8000000 in
theorem pro2 (s0 : State) (dp n sf qp ql qcap up remp : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 4) (hn1 : 1 ≤ n) (dtop : Nat) (hdtop : M.readLE (dp + n * 8 - 8) 8 = dtop) (hdt0 : dtop ≠ 0) (hdtB : dtop < 2 ^ 64)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp)
    (e2 : R 2 = BitVec.ofNat 64 n) (e9 : R 9 = BitVec.ofNat 64 dp) (e4 : R 4 = BitVec.ofNat 64 sf)
    (e0 : R 0 = BitVec.ofNat 64 qp) (e3 : R 3 = BitVec.ofNat 64 ql) (e1 : R 1 = BitVec.ofNat 64 qcap)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp)
    (hx15 : s0.xmm 15 = 0) (hqp : qp < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qcap < 2 ^ 64) (hup : up < 2 ^ 64) (hremp : remp < 2 ^ 64) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x140))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x4c), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (kr : Nat → W64),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x140), flags := fl', mem := M', kreg := kr } ∧
        R' 12 = BitVec.ofNat 64 (n - 1) ∧ R' 11 = BitVec.ofNat 64 (64 - Janus.Arm64.clzNat 64 dtop) ∧
        R' 8 = 0 - BitVec.ofNat 64 (Janus.Arm64.clzNat 64 dtop) ∧ R' 13 = BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 dtop) ∧
        R' 15 = BitVec.ofNat 64 (Janus.Arm64.clzNat 64 dtop) ∧ (∀ k, k ∉ [8, 11, 12, 13, 15] → R' k = R k) ∧
        M'.readLE (sf + 0xd8) 8 = 64 - Janus.Arm64.clzNat 64 dtop ∧ M'.readLE (sf + 0xe0) 8 = n - 1 ∧
        M'.readLE (sf + 0xf8) 8 = qp ∧ M'.readLE (sf + 0x100) 8 = ql ∧ M'.readLE (sf + 0x108) 8 = qcap ∧
        M'.readLE (sf + 0x110) 8 = up ∧ M'.readLE (sf + 0x130) 8 = remp ∧
        (∀ j, j < 4 → M'.readLE (sf + 0x98 + 8 * j) 8 = 0) ∧
        MemFrame M M' [(sf + 0x98, sf + 0xb8), (sf + 0xd8, sf + 0xe8), (sf + 0xf8, sf + 0x118), (sf + 0x130, sf + 0x138)]) := by
  have hcode := ku_lt
  obtain ⟨hs63, hn1', hn2'⟩ := Fv256.B.clz_norm dtop hdt0 hdtB
  have t0 : (R 0).toNat = qp := by rw [e0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hqp
  have t3 : (R 3).toNat = ql := by rw [e3, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hql
  have t1 : (R 1).toNat = qcap := by rw [e1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hqc
  have t7 : (R 7).toNat = up := by rw [e7, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hup
  have t10 : (R 10).toNat = remp := by rw [e10, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hremp
  janus64_run [e2, e9, e4, hdtop, hdt0] until [ku + 0x140]
  all_goals (try simp only [hdt0, if_false, ite_false, ↓reduceIte])
  all_goals refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals generalize Janus.Arm64.clzNat 64 dtop = sv at *
  all_goals first
    | (simp [setRegF]; bv_omega)
    | (simp [setRegF]; done)
    | (simp [setRegF]; congr 1; omega)
    | (intro k hk
       have hk' : k ≠ 8 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 ∧ k ≠ 15 := by simpa using hk
       simp [setRegF, hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, hk'.2.2.2.2])
    | janus_frame
    | (intro j hj
       have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
       rcases hj' with rfl | rfl | rfl | rfl <;>
       simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside] <;>
       (try simp [hx15]))
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
       first
       | (simp only [Nat.reducePow]; done)
       | (simp only [Nat.reducePow]; rw [Nat.mod_eq_of_lt (by omega)] <;> omega)
       | skip)

set_option maxHeartbeats 8000000 in
theorem den_nil (s0 : State) (sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (e4 : R 4 = BitVec.ofNat 64 sf) (m_130 : M.readLE (sf + 0x130) 8 = 0) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x394))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x2e5), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x394), flags := fl', mem := M } ∧ (∀ k, k ≠ 2 → R' k = R k)) := by
  have hcode := ku_lt
  janus64_run [e4, m_130]
  refine ⟨_, _, rfl, ?_⟩
  intro k hk
  simp [setRegF, hk]

set_option maxHeartbeats 16000000 in
theorem ulen_lt_ne {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up remp n ulen sf ra rbpv : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 4) (hulen : ulen < n) (hremne : remp ≠ 0) (hremB : remp < 2 ^ 64)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true) (hrem : remp + 32 ≤ 2 ^ 48) (hra : M.accessible remp 32 true = true)
    (hdisj : remp + 32 ≤ up ∨ up + 8 * L ≤ remp)
    (hsf : sf + 0xf8 ≤ 2 ^ 48) (hsf0 : 0x60 ≤ sf) (hMs : M.accessible (sf - 0x58) 0x150 true = true)
    (hsu : up + 8 * L ≤ sf - 0x58 ∨ sf + 0xf8 ≤ up) (hsr : remp + 32 ≤ sf - 0x58 ∨ sf + 0xf8 ≤ remp)
    (e12 : R 12 = BitVec.ofNat 64 ulen) (e2 : R 2 = BitVec.ofNat 64 n) (e6 : R 6 = BitVec.ofNat 64 L)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_e8 : M.readLE (sf + 0xe8) 8 = rbpv) (m_f0 : M.readLE (sf + 0xf0) 8 = ra) (hra47 : ra < 2 ^ 47) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 ra)
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 ra, flags := fl', xmm := X', mem := M' } ∧
        R' 4 = BitVec.ofNat 64 (sf + 0xf8) ∧ R' 5 = BitVec.ofNat 64 rbpv ∧ X' 15 = s0.xmm 15 ∧ R' 14 = R 14 ∧
        (∀ j, j < 4 → M'.readLE (remp + 8 * j) 8 = M.readLE (up + 8 * j) 8) ∧
        MemFrame M M' [(sf - 8, sf), (remp, remp + 32)]) := by
  have hcode := ku_lt
  have hra2 : M.readLE (sf + 0xf0) 8 < 2 ^ 47 := by rw [m_f0]; exact hra47
  have hLc : L = 4 ∨ L = 5 ∨ L = 6 ∨ L = 7 ∨ L = 8 := by omega
  rcases hLc with rfl | rfl | rfl | rfl | rfl <;>
  (
    janus64_run [e12, e2, e6, e7, e10, e4, m_e8, m_f0, hra2]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; bv_omega
    · simp [setRegF]
    · simp [setXmmF]
    · simp [setRegF]
    · intro j hj
      have h0 := Janus.Arm64.Memory.readLE_lt M up 16
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj' with rfl | rfl | rfl | rfl
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
        simpa using Fv256.B.rd16_lo M up
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
        simpa using Fv256.B.rd16_hi M up
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
        simpa using Fv256.B.rd16_lo M (up + 16)
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
        simpa using Fv256.B.rd16_hi M (up + 16)
    · janus_frame
  )

set_option maxHeartbeats 8000000 in
theorem ulen_lt_nil (s0 : State) (n ulen sf ra rbpv : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 4) (hulen : ulen < n)
    (hsf : sf + 0xf8 ≤ 2 ^ 48) (hsf0 : 0x60 ≤ sf) (hMs : M.accessible sf 0xf8 true = true)
    (e12 : R 12 = BitVec.ofNat 64 ulen) (e2 : R 2 = BitVec.ofNat 64 n) (e10 : R 10 = 0#64) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_e8 : M.readLE (sf + 0xe8) 8 = rbpv) (m_f0 : M.readLE (sf + 0xf0) 8 = ra) (hra47 : ra < 2 ^ 47) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 ra)
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 ra, flags := fl', mem := M } ∧
        R' 4 = BitVec.ofNat 64 (sf + 0xf8) ∧ R' 5 = BitVec.ofNat 64 rbpv ∧ R' 14 = R 14) := by
  have hcode := ku_lt
  have hra2 : M.readLE (sf + 0xf0) 8 < 2 ^ 47 := by rw [m_f0]; exact hra47
  janus64_run [e12, e2, e10, e4, m_e8, m_f0, hra2]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · simp [setRegF]; bv_omega
  · simp [setRegF]
  · simp [setRegF]

set_option maxHeartbeats 8000000 in
theorem pro1 (s0 : State) (sp0 dp : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hsp0 : 0x150 ≤ sp0) (hsp : sp0 + 0x48 ≤ 2 ^ 48) (hMs : M.accessible (sp0 - 0x148) 0x190 true = true)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true) (hdisj : dp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ dp)
    (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48) (hg2 : M.accessible ((R 14).toNat + 16) 8 false = true)
    (hg3 : M.readLE ((R 14).toNat + 16) 8 < sp0 - 0x70) (hgd : (R 14).toNat + 24 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ (R 14).toNat + 16)
    (e4 : R 4 = BitVec.ofNat 64 sp0) (e9 : R 9 = BitVec.ofNat 64 dp) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x34))
      { s0 with regs := R, rip := BitVec.ofNat 64 ku, flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x34), flags := fl', mem := M' } ∧
        R' 2 = BitVec.ofNat 64 4 - 1 ∧ R' 4 = BitVec.ofNat 64 (sp0 - 0xf0) ∧ R' 5 = BitVec.ofNat 64 (sp0 - 8) ∧
        (∀ k, k ∉ [2, 4, 5, 12] → R' k = R k) ∧
        M'.readLE (sp0 - 8) 8 = (R 5).toNat ∧ M'.readLE (sp0 + 8) 8 = (R 0).toNat ∧ M'.readLE (sp0 + 32) 8 = (R 7).toNat ∧
        MemFrame M M' [(sp0 - 8, sp0), (sp0 + 8, sp0 + 16), (sp0 + 32, sp0 + 40)]) := by
  have hcode := ku_lt
  janus64_run [e4, e9] until [ku + 0x34]
  have t5 := (R 5).isLt
  have t0 := (R 0).isLt
  have t7 := (R 7).isLt
  simp only [Nat.reducePow] at t5 t0 t7
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]; bv_omega
  · simp [setRegF]; bv_omega
  · intro k hk
    have : k ≠ 2 ∧ k ≠ 4 ∧ k ≠ 5 ∧ k ≠ 12 := by simp at hk; omega
    simp [setRegF, this.1, this.2.1, this.2.2.1, this.2.2.2]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega)
  · janus_frame

end Fv256.Amd64.UdivremG
