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

namespace Fv256.Arm64.KnuthPost
abbrev kn : Nat := segAddr Fv256.Arm64.ChainProg.program "github.com/holiman/uint256.udivremKnuth"

set_option maxHeartbeats 8000000 in
/-- after the multiply-subtract loop: `u[j+n] = u2 - borrow`; no add-back needed (`borrow ≤ u2`). -/
theorem post_sub_ok (s0 : State) (up j n b u2 : Nat) (M : Memory)
    (hb : b ≤ u2) (hu2 : u2 < 2 ^ 64)
    (hua : M.accessible (up + 8 * (j + n)) 8 true = true) (hub : up + 8 * (j + n) + 8 ≤ 2 ^ 48)
    (e1 : s0.regs 1 = BitVec.ofNat 64 (j + n)) (e9 : s0.regs 9 = BitVec.ofNat 64 up)
    (e13 : s0.regs 13 = BitVec.ofNat 64 u2) (e15 : s0.regs 15 = BitVec.ofNat 64 b)
    (hmem : s0.mem = M) (hpc : s0.pc = BitVec.ofNat 64 (kn + 0x1b0)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x1cc)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x1cc), flags := fl', mem := M' } ∧
        M'.readLE (up + 8 * (j + n)) 8 = u2 - b ∧
        MemFrame M M' [(up + 8 * (j + n), up + 8 * (j + n) + 8)] ∧
        (∀ k, k ∉ [11] → R' k = s0.regs k)) := by
  have hb2 : b < 2 ^ 64 := by omega
  have hbs : ¬ (BitVec.ofNat 64 u2).toNat < (BitVec.ofNat 64 b).toNat := by
    simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hu2, Nat.mod_eq_of_lt hb2]; omega
  subst hmem
  janus_run [e1, e9, e13, e15, hb, hbs] until [kn + 0x1cc]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
  · rw [show up + (j + n) * 8 = up + 8 * (j + n) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    omega
  · exact (MemFrame.refl _ _).writeLE _ (r := (up + 8 * (j + n), up + 8 * (j + n) + 8)) (by simp) (by simp <;> omega) (by simp <;> omega)
  · intro k hk
    have hk' : k ≠ 11 := by simpa using hk
    simp [setReg_apply, hk']
set_option maxHeartbeats 8000000 in
/-- after the multiply-subtract loop with `u2 < borrow`: `u[j+n] = u2 - borrow mod 2^64`, enter the add-back loop with carry 0. -/
theorem post_sub_borrow (s0 : State) (up j n b u2 : Nat) (M : Memory)
    (hb : u2 < b) (hb2 : b < 2 ^ 64)
    (hua : M.accessible (up + 8 * (j + n)) 8 true = true) (hub : up + 8 * (j + n) + 8 ≤ 2 ^ 48)
    (e1 : s0.regs 1 = BitVec.ofNat 64 (j + n)) (e9 : s0.regs 9 = BitVec.ofNat 64 up)
    (e13 : s0.regs 13 = BitVec.ofNat 64 u2) (e15 : s0.regs 15 = BitVec.ofNat 64 b)
    (hmem : s0.mem = M) (hpc : s0.pc = BitVec.ofNat 64 (kn + 0x1b0)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x210)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x210), flags := fl', mem := M' } ∧
        R' 11 = 0 ∧ R' 13 = 0 ∧
        M'.readLE (up + 8 * (j + n)) 8 = 2 ^ 64 - b + u2 ∧
        MemFrame M M' [(up + 8 * (j + n), up + 8 * (j + n) + 8)] ∧
        (∀ k, k ∉ [11, 13] → R' k = s0.regs k)) := by
  have hu2 : u2 < 2 ^ 64 := by omega
  have hbs : (BitVec.ofNat 64 u2).toNat < (BitVec.ofNat 64 b).toNat := by
    simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hu2, Nat.mod_eq_of_lt hb2]; omega
  subst hmem
  janus_run [e1, e9, e13, e15, hb, hbs] until [kn + 0x210]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setReg_apply]
  · simp [setReg_apply]
  · rw [show up + (j + n) * 8 = up + 8 * (j + n) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    omega
  · exact (MemFrame.refl _ _).writeLE _ (r := (up + 8 * (j + n), up + 8 * (j + n) + 8)) (by simp) (by simp <;> omega) (by simp <;> omega)
  · intro k hk
    have hk' : k ≠ 11 ∧ k ≠ 13 := by simpa using hk
    simp [setReg_apply, hk'.1, hk'.2]

set_option maxHeartbeats 8000000 in
/-- after the add-back loop: add the carry into `u[j+n]` and decrement the quotient digit (X14). -/
theorem post_add (s0 : State) (up j n c w : Nat) (M : Memory)
    (hc : c ≤ 1) (hw : w < 2 ^ 64)
    (hua : M.accessible (up + 8 * (j + n)) 8 true = true) (hub : up + 8 * (j + n) + 8 ≤ 2 ^ 48)
    (e1 : s0.regs 1 = BitVec.ofNat 64 (j + n)) (e9 : s0.regs 9 = BitVec.ofNat 64 up)
    (e13 : s0.regs 13 = BitVec.ofNat 64 c) (hw' : M.readLE (up + 8 * (j + n)) 8 = w)
    (hmem : s0.mem = M) (hpc : s0.pc = BitVec.ofNat 64 (kn + 0x218)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x1cc)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x1cc), flags := fl', mem := M' } ∧
        R' 14 = s0.regs 14 - 1#64 ∧
        M'.readLE (up + 8 * (j + n)) 8 = (w + c) % 2 ^ 64 ∧
        MemFrame M M' [(up + 8 * (j + n), up + 8 * (j + n) + 8)] ∧
        (∀ k, k ∉ [11, 14] → R' k = s0.regs k)) := by
  subst hmem
  have hw'' : s0.mem.readLE (up + (j + n) * 8) 8 = w := by rw [show up + (j + n) * 8 = up + 8 * (j + n) by omega]; exact hw'
  janus_run [e1, e9, e13, hw'', hw'] until [kn + 0x1cc]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setReg_apply]
  · rw [show up + (j + n) * 8 = up + 8 * (j + n) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    omega
  · exact (MemFrame.refl _ _).writeLE _ (r := (up + 8 * (j + n), up + 8 * (j + n) + 8)) (by simp) (by simp <;> omega) (by simp <;> omega)
  · intro k hk
    have hk' : k ≠ 11 ∧ k ≠ 14 := by simpa using hk
    simp [setReg_apply, hk'.1, hk'.2]

set_option maxHeartbeats 8000000 in
/-- store the quotient digit `quot[j] = X14`, decrement `j`, back to the loop head. -/
theorem tail_store (s0 : State) (qp ql j q : Nat) (M : Memory)
    (hj : j < ql) (hq : q < 2 ^ 64) (hql : ql < 2 ^ 20)
    (hqa : M.accessible qp (8 * ql) true = true) (hqb : qp + 8 * ql ≤ 2 ^ 48)
    (hal : s0.sp.toNat % 16 = 0) (hspb : s0.sp.toNat + 120 ≤ 2 ^ 48)
    (e3 : s0.regs 3 = BitVec.ofNat 64 j) (e14 : s0.regs 14 = BitVec.ofNat 64 q)
    (m96 : M.readLE (s0.sp.toNat + 96) 8 = ql) (m88 : M.readLE (s0.sp.toNat + 88) 8 = qp)
    (hs96 : M.accessible (s0.sp.toNat + 96) 8 false = true) (hs88 : M.accessible (s0.sp.toNat + 88) 8 false = true)
    (hmem : s0.mem = M) (hpc : s0.pc = BitVec.ofNat 64 (kn + 0x1cc)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0xbc)) s0
      (fun S => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0xbc), flags := fl', mem := M' } ∧
        R' 3 = BitVec.ofNat 64 j - 1#64 ∧
        M'.readLE (qp + 8 * j) 8 = q ∧
        MemFrame M M' [(qp + 8 * j, qp + 8 * j + 8)] ∧
        (∀ k, k ∉ [1, 3, 11] → R' k = s0.regs k)) := by
  subst hmem
  have hbr : s0.mem.readLE (s0.sp.toNat + 96) 8 = ql := m96
  janus_run [e3, e14, m96, m88] until [kn + 0xbc]
  refine ReachesRet.done (by simp [kn]; rfl) ?_
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setReg_apply]
  · rw [show qp + j * 8 = qp + 8 * j by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt hq
  · rw [show qp + j * 8 = qp + 8 * j by omega]
    exact (MemFrame.refl _ _).writeLE _ (r := (qp + 8 * j, qp + 8 * j + 8)) (by simp) (by simp <;> omega) (by simp <;> omega)
  · intro k hk
    have hk' : k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 11 := by simpa using hk
    simp [setReg_apply, hk'.1, hk'.2.1, hk'.2.2]

end Fv256.Arm64.KnuthPost
