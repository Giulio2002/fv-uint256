import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.CodeIn
import Fv256.UmulProg
import Fv256.ModProg
import Fv256.ChainProg
import Fv256.RecipProg
import Fv256.ReduceProg
import Fv256.Amd64.UmulSum
import Fv256.Amd64.ModSum
import Fv256.Amd64.UdivremL
import Fv256.Amd64.RecipSummary
import Fv256.Amd64.ReduceSpec
import Fv256.Arm64.MulModLem
import Fv256.Amd64.MulModLemA
import Fv256.Amd64.MulModDefsA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModSum

set_option maxRecDepth 100000 in
theorem hcUmulProg : Janus.Contracts.EqHashModel.CodeIn64 Fv256.UmulProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcRecip : Janus.Contracts.EqHashModel.CodeIn64 Fv256.RecipProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcR4 : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ReduceProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem correctness_param (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m]
      (fun s => StackGuardOK s 0x2f0 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x28 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        Apart z.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart x.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart y.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart m.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x378) 0x3a0)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat),
          ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x28)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdm hsp
  simp only [valueAt]
  janus64_run [Fv256.Amd64.MulModLemA.copy40x, Fv256.Amd64.MulModLemA.sub312_8, Fv256.Arm64.MulModLem.ge192, Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero4, Fv256.F.wv_zero4', false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcUmulProg Fv256.Amd64.UmulSum.umul_summary,
    Fv256.CodeIn.lib_summary hcMod Fv256.Amd64.ModSum.mod_summary,
    Fv256.CodeIn.lib_summary hcChain (Fv256.Amd64.UdivremL.udivrem_rem_L (L := 8) (by omega)),
    Fv256.CodeIn.lib_summary hcRecip Fv256.Amd64.MulModDefsA.recipU,
    Fv256.CodeIn.lib_summary hcR4 hR4]
  · refine ⟨?_, ?_⟩
    · simp [Fv256.F.mulmodSpec]
    · janus_frame
  · refine ⟨?_, ?_⟩
    · simp_all [Fv256.F.mulmodSpec]
    · janus_frame
  · refine ⟨?_, ?_⟩
    · simp_all [Fv256.F.mulmodSpec]
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Amd64.MulModLemA.tail_modA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by janus_assumption) (by janus_assumption)
        (by janus_assumption) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Arm64.MulModLem.tail_udiv _ _ _ _ _ _ _ _ _ _ _ _ _ (Fv256.Amd64.MulModLemA.nz3A _ _ _ _ (by janus_assumption) (by janus_assumption))
        (by janus_assumption) (by janus_assumption) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Arm64.MulModLem.tail_r4 _ _ _ _ _ _ (Fv256.Arm64.MulModLem.nz4 _ _ _ _ (by janus_assumption))
        (by janus_assumption) (by janus_assumption)
    · janus_frame

end Fv256.Amd64.MulModSum
