import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.KnuthSub

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub

namespace Fv256.Amd64.KnuthTail

set_option maxHeartbeats 8000000 in
theorem tail_nb (s0 : State) (up dp qp n m j ql v dl dh cap u2 b qh : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20) (hql : j < ql) (hql2 : ql < 2 ^ 20)
    (hs : (R 4).toNat + 0x90 ≤ 2 ^ 48)
    (hMs : M.accessible (R 4).toNat 0x90 true = true)
    (hua : M.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
    (hqa : M.accessible qp (8 * ql) true = true) (hqb : qp + 8 * ql ≤ 2 ^ 48)
    (hsu : up + 8 * m ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ up) (hsq : qp + 8 * ql ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ qp)
    (hqu : qp + 8 * ql ≤ up ∨ up + 8 * m ≤ qp)
    (hbu : b ≤ u2) (hu2B : u2 < 2 ^ 64) (hbB : b < 2 ^ 64) (hqhB : qh < 2 ^ 64)
    (e2 : R 2 = BitVec.ofNat 64 u2) (e13 : R 13 = BitVec.ofNat 64 b) (e3 : R 3 = BitVec.ofNat 64 qh) (e12 : R 12 = BitVec.ofNat 64 m)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 n)
    (hm38 : M.readLE ((R 4).toNat + 0x38) 8 = j + n) (hm60 : M.readLE ((R 4).toNat + 0x60) 8 = ql)
    (hm28 : M.readLE ((R 4).toNat + 0x28) 8 = j) (hm58 : M.readLE ((R 4).toNat + 0x58) 8 = qp)
    (hm40 : M.readLE ((R 4).toNat + 0x40) 8 = n - 1) (hm30 : M.readLE ((R 4).toNat + 0x30) 8 = dl) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0xd1))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0x23a), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl', mem := (Janus.Arm64.Memory.writeLE M (up + (j + n) * 8) 8 (2 ^ 64 - b + u2)).writeLE (qp + j * 8) 8 qh } ∧
        R' 1 = BitVec.ofNat 64 (n - 1) ∧ R' 3 = BitVec.ofNat 64 ql ∧ R' 6 = BitVec.ofNat 64 j - 1 ∧
        R' 11 = BitVec.ofNat 64 dl ∧ R' 13 = BitVec.ofNat 64 m ∧
        (∀ k, k ∉ [1, 2, 3, 6, 11, 12, 13] → R' k = R k)) := by
  have hcode := kn_lt
  janus64_run [e2, e13, e3, e12, e7, e10, hm38, hm60, hm28, hm58, hm40, hm30]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 6 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by simpa using hk
       obtain ⟨k1, k2, k3, k6, k11, k12, k13⟩ := hk'
       simp [setRegF, k1, k2, k3, k6, k11, k12, k13]; done)

set_option maxHeartbeats 8000000 in
theorem tail_b1 (s0 : State) (up dp qp n m j ql v dl dh cap u2 b qh : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
    (hs : (R 4).toNat + 0x90 ≤ 2 ^ 48)
    (hMs : M.accessible (R 4).toNat 0x90 true = true)
    (hua : M.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
    (hsu : up + 8 * m ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ up)
    (hbu : u2 < b) (hu2B : u2 < 2 ^ 64) (hbB : b < 2 ^ 64)
    (e2 : R 2 = BitVec.ofNat 64 u2) (e13 : R 13 = BitVec.ofNat 64 b) (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 n)
    (hm38 : M.readLE ((R 4).toNat + 0x38) 8 = j + n) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0x2a2))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0x23a), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x2a2), flags := fl', mem := Janus.Arm64.Memory.writeLE M (up + (j + n) * 8) 8 (2 ^ 64 - b + u2) } ∧
        R' 1 = BitVec.ofNat 64 (j + n) ∧ R' 2 = 0 ∧ R' 11 = 0 ∧
        (∀ k, k ∉ [1, 2, 11] → R' k = R k)) := by
  have hcode := kn_lt
  janus64_run [e2, e13, e7, e10, hm38]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 11 := by simpa using hk
       obtain ⟨k1, k2, k11⟩ := hk'
       simp [setRegF, k1, k2, k11]; done)

set_option maxHeartbeats 8000000 in
theorem tail_b2 (s0 : State) (up dp qp n m j ql v dl dh cap qh c : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20) (hql : j < ql) (hql2 : ql < 2 ^ 20)
    (hs : (R 4).toNat + 0x90 ≤ 2 ^ 48)
    (hMs : M.accessible (R 4).toNat 0x90 true = true)
    (hua : M.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
    (hqa : M.accessible qp (8 * ql) true = true) (hqb : qp + 8 * ql ≤ 2 ^ 48)
    (hsu : up + 8 * m ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ up) (hsq : qp + 8 * ql ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ qp)
    (hqu : qp + 8 * ql ≤ up ∨ up + 8 * m ≤ qp)
    (hc : c ≤ 1) (hqhB : qh < 2 ^ 64) (hqh1 : 1 ≤ qh)
    (e1 : R 1 = BitVec.ofNat 64 (j + n)) (e11 : R 11 = BitVec.ofNat 64 c) (e3 : R 3 = BitVec.ofNat 64 qh) (e12 : R 12 = BitVec.ofNat 64 m)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 n)
    (hm60 : M.readLE ((R 4).toNat + 0x60) 8 = ql)
    (hm28 : M.readLE ((R 4).toNat + 0x28) 8 = j) (hm58 : M.readLE ((R 4).toNat + 0x58) 8 = qp)
    (hm40 : M.readLE ((R 4).toNat + 0x40) 8 = n - 1) (hm30 : M.readLE ((R 4).toNat + 0x30) 8 = dl) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0xd1))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0x2a7), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl', mem := (Janus.Arm64.Memory.writeLE M (up + (j + n) * 8) 8 (M.readLE (up + (j + n) * 8) 8 + c)).writeLE (qp + j * 8) 8 (qh - 1) } ∧
        R' 1 = BitVec.ofNat 64 (n - 1) ∧ R' 3 = BitVec.ofNat 64 ql ∧ R' 6 = BitVec.ofNat 64 j - 1 ∧
        R' 11 = BitVec.ofNat 64 dl ∧ R' 13 = BitVec.ofNat 64 m ∧
        (∀ k, k ∉ [1, 2, 3, 6, 11, 12, 13] → R' k = R k)) := by
  have hcode := kn_lt
  janus64_run [e1, e11, e3, e12, e7, e10, hm60, hm28, hm58, hm40, hm30]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 6 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by simpa using hk
       obtain ⟨k1, k2, k3, k6, k11, k12, k13⟩ := hk'
       simp [setRegF, k1, k2, k3, k6, k11, k12, k13]; done)

end Fv256.Amd64.KnuthTail
