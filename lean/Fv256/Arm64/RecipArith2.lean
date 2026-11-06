import Fv256.Arm64.RecipG.G_108_16c
import Fv256.Arm64.RecipBridge
import Fv256.UtilAM
import Fv256.Arm64.RecipBv
import Janus.Tactic.CarryNf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
open Fv256.F Fv256.RecipMath

theorem sum2 (s S : State) (x108r0 x108r1 x108r2 x108r3 x108r4 x108r5 x108m176 x108m240 x108m248 x108m256 : Nat)
    (h : P_108_16c s x108r0 x108r1 x108r2 x108r3 x108r4 x108r5 x108m176 x108m240 x108m248 x108m256 S)
    (b0 : x108r0 < 2 ^ 64) (b1 : x108r1 = 2 ^ 64 - 1) (b2 : x108r2 < 2 ^ 64) (b3 : x108r3 < 2 ^ 64) :
    ∃ x16cr0 x16cr7, L16c S x16cr0 x108r2 x108r3 x108r4 x108r5 x16cr7 0 x108m176 x108m240 x108m248 x108m256 ∧
      x16cr7 + 2 ^ 64 * x16cr0 = (if ((2 * (x108r0 * 2 ^ 64) + 2 ^ 128 - (2 * stage2e x108r0 x108r2 x108r3) % 2 ^ 128) % 2 ^ 128 = 0 ∧ 2 * x108r3 % 2 ^ 64 = 0)
        then 2 ^ 128 - 1 else (2 * (x108r0 * 2 ^ 64) + 2 ^ 128 - (2 * stage2e x108r0 x108r2 x108r3) % 2 ^ 128) % 2 ^ 128) ∧
      RecRegs s S ∧ RecMem s S.mem := by
  unfold P_108_16c at h
  obtain ⟨x16cr0, x16cr7, hL, h_x16cr0, h_x16cr7, hR, hM⟩ := h
  refine ⟨x16cr0, x16cr7, hL, ?_, hR, hM⟩
  simp (disch := first | janus_carry_disch | decide | omega) only [Fv256.AM.dec_le_div, Bool.toNat_true, Bool.toNat_false, Nat.reducePow] at h_x16cr0 h_x16cr7
  unfold stage2e
  rw [h_x16cr0, h_x16cr7]
  split <;> split
  all_goals trace_state
  all_goals sorry

end Fv256.Arm64.RecipSeg
