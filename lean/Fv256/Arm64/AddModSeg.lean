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

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.AddModSeg

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
theorem segA (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry) (hpre : PreS s)
    (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8)) :
    Janus.Tactic.ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x1c0)) s (fun s' => s'.pc = BitVec.ofNat 64 (Extracted.entry + 0x1c0) ∧ s'.sp = s.sp - 368 ∧
        (∀ i, i ≠ 8 → i ≠ 9 → i ≠ 16 → i ≠ 17 → i ≠ 20 → i ≠ 29 → s'.regs i = s.regs i) ∧
        s'.regs 8 = BitVec.ofNat 64 (s.mem.readLE ((s.regs 3).toNat + 24) 8) ∧ s'.regs 29 = s.sp - 376 ∧
        s'.mem = (s.mem.writeLE (s.sp.toNat - 376) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 368) 8 (s.regs 30).toNat) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  janus_run until [Extracted.entry + 0x1c0]
  all_goals (exact Janus.Tactic.ReachesRet.done (by simp [Extracted.entry]) ⟨by simp [Extracted.entry], rfl, fun i h8 h9 h16 h17 h20 h29 => by simp [setReg, h8, h9, h16, h17, h20, h29], by simp [setReg], by simp [setReg], rfl⟩)

end Fv256.Arm64.AddModSeg
