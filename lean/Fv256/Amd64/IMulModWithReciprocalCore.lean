import Extracted
import Fv256.Spec
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.MulModRecProg
import Fv256.Amd64.ReduceSpec
import Fv256.Amd64.MulModRecSum
import Fv256.Arm64.MulModLem

/-!
# `(*uint256.Int).IMulModWithReciprocal` (amd64): in place, `z = (z * x) mod m` (core: conditional on the `reduce4` summary)

`IMulModWithReciprocal` is `z.MulModWithReciprocal(z, x, m, mu)`; the callee is used through `Fv256.Amd64.MulModRecSum.mulmodrec_summary` over `Fv256.MulModRecProg.program`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IMulModWithReciprocalCore

set_option maxRecDepth 100000 in
theorem hcMM : Janus.Contracts.EqHashModel.CodeIn64 Fv256.MulModRecProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

abbrev Pre (z x m mu : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x2d0 ∧ 0x328 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x320 8 ∧
    Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s m 32 false ∧ Buffer s mu 40 false ∧
    Apart z.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
    Apart x.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
    Apart m.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
        Apart mu.toNat 40 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
        Fv256.F.MuOK (valueAt s m 32) (s.mem.readLE mu.toNat 40) ∧
    Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x320) 0x328

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem correctness_param (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) (z x m : BitVec 64) (mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m, mu] (Pre z x m mu)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x320, (s.regs regSP).toNat)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨huw, hu⟩, hdz, hdx, hdm, hdu, hmu, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hdm hdu hsp
  simp only [valueAt] at hmu ⊢
  unfold Fv256.F.MuOK at hmu
  rw [Util.readLE_32] at hmu
  by_cases hd : Arm64.Memory.readLE s.mem (m.toNat + 24) 8 = 0
  · janus64_run [hd, Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcMM (Fv256.Amd64.MulModRecSum.mulmodrec_small hR4)]
    refine ⟨by janus_assumption, ?_⟩
    janus_frame
  · have hmu2 := hmu (Fv256.Arm64.MulModLem.ge192' _ _ _ _ hd)
    unfold Fv256.F.RecipWeak at hmu2
    simp only [Nat.reducePow] at hmu2
    janus64_run [hmu2, Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcMM (Fv256.Amd64.MulModRecSum.mulmodrec_big hR4)]
    refine ⟨by janus_assumption, ?_⟩
    janus_frame

end Fv256.Amd64.IMulModWithReciprocalCore
