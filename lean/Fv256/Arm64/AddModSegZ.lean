import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.UtilMDO
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.ModSum
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.ChainProg
import Fv256.Arm64.ModProg
import Fv256.Arm64.CodeIn
import Fv256.UtilAM
import Fv256.Amd64.AddModTac
import Janus.Tactic.CarryNf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.AddModSegZ

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ModProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev PreS (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 816 ∧
    s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 856) 872 true = true ∧
    Extracted.program.DataLoaded s.mem ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
    (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
    (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
    (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
    (s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 32 false = true ∧
    ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
    ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
    ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat) ∧
    ((s.regs 3).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 3).toNat) ∧
    (s.regs 0 = s.regs 3 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 32 ≤ (s.regs 0).toNat) ∧
    (s.regs 0 = s.regs 1 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 32 ≤ (s.regs 0).toNat) ∧
    (s.regs 0 = s.regs 2 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 2).toNat ∨ (s.regs 2).toNat + 32 ≤ (s.regs 0).toNat) ∧
    ((s.regs 28).toNat + 24 ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ (s.regs 28).toNat + 16)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segBc (S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x1c0))
    (hm : ¬ (S.mem.readLE (S.regs 3).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 24) 8 = 0))
    (heq : S.regs 3 = S.regs 0)
    (hmb : (S.regs 3).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 3).toNat 32 false = true)
    (hsal : S.sp.toNat % 16 = 0) (hsc : S.sp.toNat + 384 ≤ 2 ^ 48)
    (hcl : S.mem.accessible (S.sp.toNat + 328) 32 true = true)
    (hdm : (S.regs 3).toNat + 32 ≤ S.sp.toNat + 328 ∨ S.sp.toNat + 360 ≤ (S.regs 3).toNat)
    (hr8 : S.regs 8 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 3).toNat + 24) 8)) :
    Janus.Tactic.ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x214)) S
      (fun S' => S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x214) ∧ S'.sp = S.sp ∧ S'.regs 8 = S.sp + 328#64 ∧
        (∀ i, i ≠ 8 → i ≠ 9 → i ≠ 10 → S'.regs i = S.regs i) ∧
        MemFrame S.mem S'.mem [(S.sp.toNat + 328, S.sp.toNat + 360)] ∧
        S'.mem.readLE (S.sp.toNat + 328) 32 = S.mem.readLE (S.regs 3).toNat 32) := by
  rw [heq] at hm hmb hma hdm hr8
  janus_run [heq, Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, BitVec.toNat_ofNat, Util.readLE_32] until [Extracted.entry + 0x214]
  apply Janus.Tactic.ReachesRet.done
  · simp [Extracted.entry]
  refine ⟨by simp [Extracted.entry], rfl, by simp [setReg], fun i h8 h9 h10 => by simp [setReg, h8, h9, h10], ?_, ?_⟩
  · dsimp only
    janus_frame
  · dsimp only
    rw [heq]
    simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    simp only [Nat.reducePow, Util.readLE8_mod]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segZero (S : State) (R X29 : BitVec 64) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x1c0))
    (hsal : S.sp.toNat % 16 = 0) (hsb : 368 ≤ S.sp.toNat)
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hmb : (S.regs 3).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 3).toNat 32 false = true)
    (hm : S.mem.readLE (S.regs 3).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 24) 8 = 0)
    (hr8 : S.regs 8 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 3).toNat + 24) 8))
    (hret : S.mem.readLE S.sp.toNat 8 = R.toNat) (hRa : R.toNat % 4 = 0) (hRb : R.toNat < 2 ^ 56)
    (hdzs : (S.regs 0).toNat + 32 ≤ S.sp.toNat - 8 ∨ S.sp.toNat + 8 ≤ (S.regs 0).toNat)
    (hsw8 : S.mem.accessible (S.sp.toNat - 8) 16 false = true)
    (hx29 : S.mem.readLE (S.sp.toNat - 8) 8 = X29.toNat) :
    Janus.Tactic.ReachesRet Extracted.program R S
      (fun S' => S'.pc = R ∧ S'.sp = S.sp + 368 ∧ S'.regs 0 = S.regs 0 ∧ S'.regs 28 = S.regs 28 ∧ S'.regs 29 = X29 ∧ S'.regs 18 = S.regs 18 ∧ S'.regs 30 = R ∧
        S'.mem.readLE (S.regs 0).toNat 32 = 0 ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32)]) := by
  janus_run [hret, hx29, Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, BitVec.toNat_ofNat, Util.readLE_32]
  janus_frame

end Fv256.Arm64.AddModSegZ
