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

namespace Fv256.Arm64.AddModSegB

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
theorem segB (S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x1c0))
    (hm : ¬ (S.mem.readLE (S.regs 3).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 24) 8 = 0))
    (hne : S.regs 3 ≠ S.regs 0)
    (hmb : (S.regs 3).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 3).toNat 32 false = true)
    (hr8 : S.regs 8 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 3).toNat + 24) 8)) :
    Janus.Tactic.ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x214)) S
      (fun S' => S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x214) ∧ S'.mem = S.mem ∧ S'.sp = S.sp ∧ S'.regs 8 = S.regs 3 ∧
        (∀ i, i ≠ 8 → i ≠ 9 → i ≠ 10 → S'.regs i = S.regs i)) := by
  janus_run [Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, BitVec.toNat_ofNat] until [Extracted.entry + 0x214]
  exact Janus.Tactic.ReachesRet.done (by simp [Extracted.entry, setReg]) ⟨by simp [Extracted.entry, setReg], rfl, rfl, by simp [setReg],
    fun i h8 h9 h10 => by simp [setReg, h8, h9, h10]⟩

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segC (S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x214))
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hxb : (S.regs 1).toNat + 32 ≤ 2 ^ 48) (hxa : S.mem.accessible (S.regs 1).toNat 32 false = true)
    (hyb : (S.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : S.mem.accessible (S.regs 2).toNat 32 false = true)
    (hzx : S.regs 0 = S.regs 1 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 1).toNat ∨ (S.regs 1).toNat + 32 ≤ (S.regs 0).toNat)
    (hzy : S.regs 0 = S.regs 2 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 2).toNat ∨ (S.regs 2).toNat + 32 ≤ (S.regs 0).toNat)
    (hnov : S.mem.readLE (S.regs 1).toNat 32 + S.mem.readLE (S.regs 2).toNat 32 < 2 ^ 256) :
    Janus.Tactic.ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x318)) S
      (fun S' => True) := by
  by_cases e1 : S.regs 0 = S.regs 1 <;> by_cases e2 : S.regs 0 = S.regs 2
  · have e1n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e1]
    have e2n : (S.regs 2).toNat = (S.regs 0).toNat := by rw [← e2]
    janus_run [Util.readLE_32, e1n, e2n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals (trace_state; sorry)
  · have hzy' := hzy.resolve_left e2
    have e1n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e1]
    janus_run [Util.readLE_32, e1n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals (trace_state; sorry)
  · have hzx' := hzx.resolve_left e1
    have e2n : (S.regs 2).toNat = (S.regs 0).toNat := by rw [← e2]
    janus_run [Util.readLE_32, e2n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals (trace_state; sorry)
  · have hzx' := hzx.resolve_left e1
    have hzy' := hzy.resolve_left e2
    janus_run [Util.readLE_32] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals (trace_state; sorry)

end Fv256.Arm64.AddModSegB
