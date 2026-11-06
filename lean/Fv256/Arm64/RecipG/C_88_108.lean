import Fv256.Arm64.RecipG.G_88_bc
import Fv256.Arm64.RecipG.G_bc_108

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def PC_88_108 (s : State) (x88m32 x88m40 x88m48 x88m56 x88m176 : Nat) (S' : State) : Prop :=
  ∃ xbcr0 x108r0 x108m176, L108 S' x108r0 18446744073709551615 x88m48 x88m56 x88m32 x88m40 x108m176 x88m32 x88m40 x88m48 ∧ xbcr0 = (if x88m56 / 2 ^ 32 % 2 ^ 32 = 2 ^ 31 then 2 ^ 64 - 1 else 2 ^ 63 / (x88m56 / 2 ^ 32)) ∧ x108r0 = (if (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * x88m56 / 18446744073709551616 + xbcr0 * 4294967296 % 18446744073709551616 + (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * x88m56 / 18446744073709551616 + xbcr0 * 4294967296 % 18446744073709551616)) % 18446744073709551616 ||| x88m56 * 2 % 18446744073709551616 = 0 then 18446744073709551615 else (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * x88m56 / 18446744073709551616 + xbcr0 * 4294967296 + (18446744073709551616 - xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * x88m56 / 18446744073709551616 + xbcr0 * 4294967296)) % 18446744073709551616) ∧ x108m176 = (18446744073709551615 + x88m176 % 64) % 18446744073709551616 ∧ xbcr0 % 2 ^ 32 = r0f x88m56 ∧ 2 ^ 63 ≤ x88m56 ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem c_88_108 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0x88)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) (x88m32 x88m40 x88m48 x88m56 x88m176 : Nat) (hL : L88 S x88m32 x88m40 x88m48 x88m56 x88m176) (hX0 : 2 ^ 63 ≤ x88m56) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x108)) S (PC_88_108 s x88m32 x88m40 x88m48 x88m56 x88m176) := by
  refine Fv256.Arm64.SegCompose.seg_trans (g_88_bc s S hpc hs hR hM x88m32 x88m40 x88m48 x88m56 x88m176 hL hX0) ?_
  intro S1 hpc1 hq1
  unfold P_88_bc at hq1
  obtain ⟨xbcr0, hL1, h_xbcr0, hx1_0, hx1_1, hR1, hM1⟩ := hq1
  refine Fv256.Arm64.SegCompose.seg_mono (g_bc_108 s S1 hpc1 hs hR1 hM1 xbcr0 x88m56 x88m32 x88m40 x88m48 x88m176 hL1 hx1_0 hx1_1) ?_
  intro S2 hq2
  unfold P_bc_108 at hq2
  obtain ⟨x108r0, x108m176, hL2, h_x108r0, h_x108m176, hR2, hM2⟩ := hq2
  unfold PC_88_108
  exact ⟨xbcr0, x108r0, x108m176, hL2, h_xbcr0, h_x108r0, h_x108m176, hx1_0, hx1_1, hR2, hM2⟩

end Fv256.Arm64.RecipSeg
