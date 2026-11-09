import Fv256.Proofs.Common.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Amd64.KnuthSub

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub

namespace Fv256.Amd64.KnuthOvf

set_option maxHeartbeats 8000000 in
theorem est_ovf (s0 : State) (up dp n m j v dl dh u2 u1 u0 : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
    (hdh : 2 ^ 63 ≤ dh) (hdh2 : dh < 2 ^ 64)
    (hs : (R 4).toNat + 0x90 ≤ 2 ^ 48)
    (hMs : M.accessible (R 4).toNat 0x90 true = true)
    (hua : M.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
    (hda : M.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hsu : up + 8 * m ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ up) (hsd : dp + 8 * n ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ dp)
    (hge : dh ≤ u2) (hu2B : u2 < 2 ^ 64)
    (hcap : m ≤ (R 8).toNat) (hcapB : (R 8).toNat < 2 ^ 55)
    (e0 : R 0 = BitVec.ofNat 64 v) (e6 : R 6 = BitVec.ofNat 64 j) (e7 : R 7 = BitVec.ofNat 64 up) (e9 : R 9 = BitVec.ofNat 64 dp)
    (e10 : R 10 = BitVec.ofNat 64 n) (e11 : R 11 = BitVec.ofNat 64 dl) (e13 : R 13 = BitVec.ofNat 64 m)
    (e15 : R 15 = BitVec.ofNat 64 dh) (e1 : R 1 = BitVec.ofNat 64 (n - 1))
    (hu2 : M.readLE (up + (j + n) * 8) 8 = u2) (hu1 : M.readLE (up + (j + (n - 1)) * 8) 8 = u1) (hu0 : M.readLE (up + (j + (n - 2)) * 8) 8 = u0) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0x235))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x235), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 v ∧ R' 1 = BitVec.ofNat 64 (n - 1) ∧ R' 2 = BitVec.ofNat 64 u2 ∧
        R' 3 = BitVec.ofNat 64 (2 ^ 64 - 1) ∧
        R' 6 = BitVec.ofNat 64 (up + 8 * j) ∧ R' 9 = BitVec.ofNat 64 dp ∧ R' 11 = 0 ∧ R' 12 = BitVec.ofNat 64 m ∧ R' 13 = 0 ∧
        (∀ k, k ∉ [0, 1, 2, 3, 6, 9, 11, 12, 13] → R' k = R k) ∧
        M'.readLE ((R 4).toNat + 0x28) 8 = j ∧ M'.readLE (R 4).toNat 8 = u2 ∧ M'.readLE ((R 4).toNat + 0x38) 8 = j + n ∧
        MemFrame M M' [((R 4).toNat, (R 4).toNat + 0x10), ((R 4).toNat + 0x18, (R 4).toNat + 0x30), ((R 4).toNat + 0x38, (R 4).toNat + 0x40)]) := by
  have hcode := kn_lt
  have hjb : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  have hnsgn : ¬ (BitVec.ofNat 64 j).msb = true := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have hsl := Fv256.B.slice_ptr j up (R 8) (by omega) hcapB
  have hge' : ¬ (u2 % 18446744073709551616 < dh) := by rw [Nat.mod_eq_of_lt hu2B]; omega
  janus64_run [e0, e6, e7, e9, e10, e11, e13, e15, e1, hnsgn, hu2, hu1, hu0, hge']
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (config := { decide := true }) only [setRegF, ↓reduceIte]; exact hsl)
    | (simp [setRegF]; done)
    | (simp [setRegF, e0, e1, e9]; done)
    | (intro k hk
       have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 6 ∧ k ≠ 9 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by simpa using hk
       obtain ⟨k0, k1, k2, k3, k6, k9, k11, k12, k13⟩ := hk'
       simp [setRegF, k0, k1, k2, k3, k6, k9, k11, k12, k13]; done)
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
       simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
    | janus_frame

end Fv256.Amd64.KnuthOvf
