import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthExit
abbrev kn : Nat := segAddr Fv256.Arm64.ChainProg.program "github.com/holiman/uint256.udivremKnuth"

set_option maxHeartbeats 8000000 in
/-- the epilogue of `udivremKnuth` (+0x1dc): restore X29 and X30 from the frame and return. -/
theorem knuth_exit (S : State) (rt : W64) (fp : Nat) (M : Memory)
    (hal : S.sp.toNat % 16 = 0) (hsp : 8 ≤ S.sp.toNat) (hspb : S.sp.toNat + 80 ≤ 2 ^ 48)
    (hmem : S.mem = M) (hpc : S.pc = BitVec.ofNat 64 (kn + 0x1dc))
    (hrt : M.readLE S.sp.toNat 8 = rt.toNat) (hfp : M.readLE (S.sp.toNat - 8) 8 = fp)
    (h4 : rt.toNat % 4 = 0) (h56 : rt.toNat < 2 ^ 56) (hrta : M.accessible S.sp.toNat 8 false = true) (hfpa : M.accessible (S.sp.toNat - 8) 8 false = true) :
    ReachesRet Fv256.Arm64.ChainProg.program rt S
      (fun S' => S'.pc = rt ∧ S'.sp = S.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 fp ∧ S'.regs 30 = rt ∧
        (∀ i, i ≠ 29 → i ≠ 30 → S'.regs i = S.regs i) ∧ S'.mem = M) := by
  subst hmem
  simp only [kn, reduceSegAddr, Nat.reduceAdd] at hpc ⊢
  have hrr : BitVec.ofNat 64 rt.toNat = rt := by simp
  janus_run [hrt, hfp, hpc, hrr]
  intro i h29 h30
  simp [h29, h30]
end Fv256.Arm64.KnuthExit
