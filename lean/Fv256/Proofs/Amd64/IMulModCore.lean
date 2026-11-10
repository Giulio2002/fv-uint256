import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.MulModProg
import Fv256.Proofs.Amd64.ReduceSpec
import Fv256.Proofs.Amd64.MulModSum
import Fv256.Proofs.Legacy.Amd64.IMulModCore

/-!
# `(*uint256.Int).IMulMod` (amd64): in place, `z = (z * x) mod m` (core: conditional on the `reduce4` summary)

`IMulMod` is `z.MulMod(z, x, m)`; the callee is used through `Fv256.Amd64.MulModSum.mulmod_summary` over `Fv256.MulModProg.program`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IMulModCore

set_option maxRecDepth 100000 in
theorem hcMM : Janus.Contracts.EqHashModel.CodeIn64 Fv256.MulModProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem correctness_param (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m] (Pre z x m)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x3a8, (s.regs regSP).toNat)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, hdz, hdx, hdm, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hdm hsp
  simp only [valueAt]
  janus64_run [Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcMM (Fv256.Amd64.MulModSum.mulmod_summary hR4)]
  refine ⟨by janus_assumption, ?_⟩
  janus_frame

end Fv256.Amd64.IMulModCore
