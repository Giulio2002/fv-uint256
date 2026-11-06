import Extracted
import Fv256.Spec
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.SqrtProg
import Fv256.Amd64.SqrtSummaryL

/-!
# `(*uint256.Int).ISqrt() *Int` (amd64): in place, `z = ⌊√z⌋`   (WIP: statement, proof pending)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ISqrt

abbrev Pre (z : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x220 ∧ 0x2a0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x210 0x10 ∧ Buffer s z 32 true ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.SqrtProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z] (Pre z)
      (fun s s' => s'.regs 0 = z ∧ Fv256.F.IsSqrt (valueAt s z 32) (valueAt s' z 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x210, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, hdz, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hsp
  simp only [valueAt]
  janus64_run [Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.SqrtLib.sqrt_summary]
  trace_state
  all_goals sorry

end Fv256.Amd64.ISqrt
