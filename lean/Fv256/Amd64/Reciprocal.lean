import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.RecipSpec
import Fv256.CodeIn
import Fv256.LshProg
import Fv256.Amd64.LshSum
import Fv256.Amd64.LshNorm

/-!
# `uint256.Reciprocal(m *Int) (mu [5]uint64)` (amd64)

**Documented behaviour.** "Reciprocal computes a 320-bit value representing 1/m", specialised to `m[3] != 0` (so
`2^192 <= m < 2^256`), "returns zero if `m[3] == 0`".  The five result words are returned in the caller's result slot (`RSP+8` on entry).

**Guarantee.** For every `m` with 32 readable bytes (below `2^48`) outside the callee window, and every Go call in which the
stack-growth check falls through, the call returns, and with `M` the number at `m` and `mu` the 320-bit result:
`M < 2^192` gives `mu = 0`; `2^192 <= M` gives `RecipWeak M mu` (`ex-3 <= mu <= ex`, `ex = (2^512-1)/M`); `2^193 <= M` gives
`RecipOK M mu` (`ex-1 <= mu <= ex`).  Nothing outside the frame window changes.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Reciprocal

set_option maxRecDepth 100000 in
theorem hcLsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.LshProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem correctness (m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m]
      (fun s => StackGuardOK s 0x1b8 ∧ 0x248 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x240 0x30 ∧ Buffer s m 32 false ∧
        Apart m.toNat 32 ((s.regs regSP).toNat - 0x240) 0x270 ∧
        Apart ((s.regs regG).toNat + 16) 8 ((s.regs regSP).toNat - 0x240) 0x270)
      (fun s s' => (valueAt s m 32 < 2 ^ 192 → s'.mem.readLE ((s.regs regSP).toNat + 8) 40 = 0) ∧
        (2 ^ 192 ≤ valueAt s m 32 → Fv256.F.RecipWeak (valueAt s m 32) (s'.mem.readLE ((s.regs regSP).toNat + 8) 40)) ∧
        (2 ^ 193 ≤ valueAt s m 32 → Fv256.F.RecipOK (valueAt s m 32) (s'.mem.readLE ((s.regs regSP).toNat + 8) 40)) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 0x240, (s.regs regSP).toNat + 0x30)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hmw, hm⟩, hdm, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdm hsp
  simp only [valueAt]
  janus64_run [Util.readLE_32] until [Extracted.entry + 0x1f3] calls [hS := Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshNorm.lsh_norm_summary (s.regs 4 - 0x220#64) m)]
  all_goals (trace_state; sorry)

end Fv256.Amd64.Reciprocal
