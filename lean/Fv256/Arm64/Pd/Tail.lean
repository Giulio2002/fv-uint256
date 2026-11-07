import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.PdCells
import Fv256.Arm64.P.T
import Fv256.Util
import Fv256.UtilB2
import Fv256.Arm64.Pd.Pad
import Fv256.Arm64.Pd.Inner

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P

namespace Fv256.Arm64.Pd

theorem or4r' (a b c d : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) (hd : d < 2 ^ 64) :
    (BitVec.ofNat 64 a ||| (BitVec.ofNat 64 b ||| (BitVec.ofNat 64 c ||| BitVec.ofNat 64 d)) = 0#64) ↔
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at h'
    have h0 : (0#64).toNat = 0 := rfl
    rw [h0] at h'
    simp only [Nat.or_eq_zero_iff] at h'
    simpa using h'
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem or4_iff_wv (M : Memory) (p y : Nat) (hy : Fv256.B.wv M p 4 = y) :
    (BitVec.ofNat 64 (M.readLE (p + 24) 8) ||| (BitVec.ofNat 64 (M.readLE (p + 16) 8) |||
      (BitVec.ofNat 64 (M.readLE (p + 8) 8) ||| BitVec.ofNat 64 (M.readLE p 8))) = 0#64) ↔ y = 0 := by
  have l0 := Janus.Arm64.Memory.readLE_lt M p 8
  have l1 := Janus.Arm64.Memory.readLE_lt M (p + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt M (p + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt M (p + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  rw [or4r' _ _ _ _ l3 l2 l1 l0]
  simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hy
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- After the inner loop with a zero quotient: the jump to the final call. -/
theorem pd_tail_z (s : State) (b : Nat) (hpc : s.pc = BitVec.ofNat 64 pdJ)
    (e4 : s.sp = BitVec.ofNat 64 b) (hb : 368 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 424 ≤ 2 ^ 48)
    (hacc : s.mem.accessible (b + 320) 32 false = true) (hy : Fv256.B.wv s.mem (b + 320) 4 = 0) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdF) s
      (fun S' => S'.sp = s.sp ∧ (∀ k, k ∉ [8, 12, 13] → S'.regs k = s.regs k) ∧ S'.mem = s.mem) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hal : s.sp.toNat % 16 = 0 := by rw [e4, BitVec.toNat_ofNat]; omega
  have hz := (or4_iff_wv s.mem (b + 320) 0 hy).2 rfl
  janus_run [e4, hal, hz] until [pdF]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_⟩
  · simp [setReg]; exact e4.symm
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- After the inner loop with a non-zero quotient: to the pad loop head with `x3 = 0`. -/
theorem pd_tail_nz (s : State) (b y' : Nat) (hpc : s.pc = BitVec.ofNat 64 pdJ)
    (e4 : s.sp = BitVec.ofNat 64 b) (hb : 368 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 424 ≤ 2 ^ 48)
    (hacc : s.mem.accessible (b + 320) 32 false = true) (hy : Fv256.B.wv s.mem (b + 320) 4 = y') (hy0 : y' ≠ 0) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdK) s
      (fun S' => S'.regs 3 = 0#64 ∧ S'.sp = s.sp ∧ (∀ k, k ∉ [3, 8, 12, 13] → S'.regs k = s.regs k) ∧ S'.mem = s.mem) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hal : s.sp.toNat % 16 = 0 := by rw [e4, BitVec.toNat_ofNat]; omega
  have hz := or4_iff_wv s.mem (b + 320) y' hy
  have hz' : ¬ (BitVec.ofNat 64 (s.mem.readLE (b + 320 + 24) 8) ||| (BitVec.ofNat 64 (s.mem.readLE (b + 320 + 16) 8) |||
      (BitVec.ofNat 64 (s.mem.readLE (b + 320 + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE (b + 320) 8))) = 0#64) :=
    fun h => hy0 (hz.1 h)
  janus_run [e4, hal, hz'] until [pdK]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_⟩
  · simp [setReg]
  · simp [setReg]; exact e4.symm
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · rfl
end Fv256.Arm64.Pd
