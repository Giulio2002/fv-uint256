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
    (b0 : x108r0 < 2 ^ 64) (b2 : x108r2 < 2 ^ 64) (b3 : x108r3 < 2 ^ 64) :
    True := by
  unfold P_108_16c at h
  obtain ⟨x16cr0, x16cr7, hL, h_x16cr0, h_x16cr7, hR, hM⟩ := h
  simp (disch := omega) only [Fv256.AM.dec_le_div, Bool.toNat_true, Bool.toNat_false, Nat.reducePow] at h_x16cr0 h_x16cr7
  trace_state
  trivial

end Fv256.Arm64.RecipSeg
