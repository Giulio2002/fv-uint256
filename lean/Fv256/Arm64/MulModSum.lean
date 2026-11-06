import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.CodeIn
import Fv256.Arm64.UmulProg
import Fv256.Arm64.UmulSum
import Fv256.Arm64.ChainProg
import Fv256.Arm64.ModProg
import Fv256.Arm64.ModSum
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.ReduceProg
import Fv256.Arm64.ReduceSpec
import Fv256.Arm64.RecipProg
import Fv256.Arm64.MulModDefs
import Fv256.Arm64.MulModLem
import Fv256.Arm64.MdorLemmas
import Fv256.Arm64.DivLemmas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulModSum

set_option maxRecDepth 200000 in
theorem hcUmul : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.UmulProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ModProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcR4 : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ReduceProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcRec : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.RecipProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)


def pre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 768 ∧ StackOK s 808 40 ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 808) 848 ∧
  ((s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧ Apart (s.regs 0).toNat 32 (s.sp.toNat - 808) 848) ∧
  ((s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 808) 848) ∧
  ((s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧ Apart (s.regs 2).toNat 32 (s.sp.toNat - 808) 848) ∧
  ((s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 32 false = true ∧ Apart (s.regs 3).toNat 32 (s.sp.toNat - 808) 848)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem mulmod_summary (hRec : Fv256.Arm64.MulModDefs.RecipSummaryU) (hR4 : Fv256.Arm64.ReduceSpec.R4Summary) :
    Summary Extracted.program Extracted.entry pre
    (fun s s' => s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 1).toNat 32)
          (s.mem.readLE (s.regs 2).toNat 32) (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 808, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 40)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hgs, ⟨hzb, hza, hzs⟩, ⟨hxb, hxa, hxs⟩, ⟨hyb, hya, hys⟩, ⟨hmb, hma, hms⟩⟩
  janus_run [Fv256.Arm64.MulModLem.copy40, Fv256.Arm64.MulModLem.sub320_8, Fv256.Arm64.MulModLem.ge192, Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.Arm64.MdorLemmas.wv_zero8w, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcUmul Fv256.Arm64.UmulSum.umul_summary,
    Janus.Contracts.EqHashModel.Summary.of_codeIn hcMod Fv256.Arm64.ModSum.mod_summary,
    Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 8) (by decide) (by decide)),
    Janus.Contracts.EqHashModel.Summary.of_codeIn hcRec hRec,
    Janus.Contracts.EqHashModel.Summary.of_codeIn hcR4 hR4]
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
    · exact Fv256.Arm64.MulModLem.tail_mod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by janus_assumption) (by janus_assumption)
        (by janus_assumption) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Arm64.MulModLem.tail_udiv _ _ _ _ _ _ _ _ _ _ _ _ _ (Fv256.Arm64.MulModLem.nz3' _ _ _ _ (by janus_assumption) (by janus_assumption))
        (by janus_assumption) (by janus_assumption) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Arm64.MulModLem.tail_r4 _ _ _ _ _ _ (Fv256.Arm64.MulModLem.nz4 _ _ _ _ (by janus_assumption))
        (by janus_assumption) (by janus_assumption)
    · janus_frame

end Fv256.Arm64.MulModSum
