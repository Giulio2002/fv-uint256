import Fv256.Proofs.Common.PrettyProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.PdCells
import Fv256.Proofs.Amd64.P.T
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Amd64.Pd.Pad
import Fv256.Proofs.Amd64.Pd.Inner

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E Fv256.Amd64.P

namespace Fv256.Amd64.Pd

theorem or4_iff_wv (M : Memory) (p y : Nat) (hy : Fv256.B.wv M p 4 = y) :
    (BitVec.ofNat 64 (M.readLE (p + 8) 8) ||| BitVec.ofNat 64 (M.readLE p 8) ||| BitVec.ofNat 64 (M.readLE (p + 16) 8) |||
      BitVec.ofNat 64 (M.readLE (p + 24) 8)).toNat = 0 ↔ y = 0 := by
  have l0 := Janus.Arm64.Memory.readLE_lt M p 8
  have l1 := Janus.Arm64.Memory.readLE_lt M (p + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt M (p + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt M (p + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  rw [Fv256.E.or4_toNat_zero_iff _ _ _ _ l1 l0 l2 l3]
  simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hy
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- After the inner loop with a zero quotient: the jump to the final call. -/
theorem pd_tail_z (s : State) (b : Nat) (hpc : s.rip = BitVec.ofNat 64 pdJ)
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (hb : 0x180 ≤ b) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hacc : s.mem.accessible (b + 0x130) 32 false = true) (hy : Fv256.B.wv s.mem (b + 0x130) 4 = 0) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdF) s
      (fun S' => (∀ k, k ∉ [2, 15] → S'.regs k = s.regs k) ∧ S'.mem = s.mem ∧ S'.xmm = s.xmm ∧ S'.df = s.df) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hz := (or4_iff_wv s.mem (b + 0x130) 0 hy).2 rfl
  have hz' : (BitVec.ofNat 64 (s.mem.readLE (b + 312) 8) ||| BitVec.ofNat 64 (s.mem.readLE (b + 304) 8) |||
      BitVec.ofNat 64 (s.mem.readLE (b + 320) 8) ||| BitVec.ofNat 64 (s.mem.readLE (b + 328) 8)).toNat = 0 := hz
  janus64_run [e4, hz'] until [pdF]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · rfl
  · rfl
  · rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- After the inner loop with a non-zero quotient: to the pad loop head with `rdx = 0`. -/
theorem pd_tail_nz (s : State) (b y' : Nat) (hpc : s.rip = BitVec.ofNat 64 pdJ)
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (hb : 0x180 ≤ b) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hacc : s.mem.accessible (b + 0x130) 32 false = true) (hy : Fv256.B.wv s.mem (b + 0x130) 4 = y') (hy0 : y' ≠ 0) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdK) s
      (fun S' => S'.regs 2 = 0#64 ∧ (∀ k, k ∉ [2, 15] → S'.regs k = s.regs k) ∧ S'.mem = s.mem ∧ S'.xmm = s.xmm ∧ S'.df = s.df) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hz := or4_iff_wv s.mem (b + 0x130) y' hy
  have hz' : ¬ (BitVec.ofNat 64 (s.mem.readLE (b + 312) 8) ||| BitVec.ofNat 64 (s.mem.readLE (b + 304) 8) |||
      BitVec.ofNat 64 (s.mem.readLE (b + 320) 8) ||| BitVec.ofNat 64 (s.mem.readLE (b + 328) 8)).toNat = 0 := fun h => hy0 (hz.1 h)
  janus64_run [e4, hz'] until [pdK]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · rfl
  · rfl
  · rfl
end Fv256.Amd64.Pd
