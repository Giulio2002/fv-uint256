import Extracted
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanA7
import Fv256.Amd64.ScanA8
import Fv256.IbsA
import Fv256.CodeIn
import Fv256.LinkEq
import Fv256.Amd64.ExpMain
import Fv256.Amd64.MoLib.Top
import Fv256.Amd64.FrameFsDf
import Fv256.Amd64.SfdLink

/-!
# `Scan` (amd64): the discharge of the callee summaries (`hibs`, `hexp`, `hmo`) from the library programs, and the two PENDING lemmas

* `disch_ibs`: `IndexByteString` (`IbsLibA`, `ibs_lib_A`), transferred with `CodeIn.lib_summary_link`.
* `disch_exp`, `disch_mo`: `ExpMain.exp_summary` / `MoLib.mo_summary` strengthened by the frame facts `fsBase`, `df` (the single pending lemma
  `Fv256.FrameFsDf.Steps_fs` + the `df` conjunct of `mo_summary`), then transferred.
* `disch_sfd`: `SetFromDecimal` (the single pending lemma, FV-I5's `SfdLib.hsfd_of_link`).
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSfd Fv256.Amd64.ScanA

namespace Fv256.Amd64.ScanDisch

set_option maxRecDepth 100000 in
theorem hcIbs : Janus.Contracts.EqHashModel.CodeIn64 Fv256.IbsProgA.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcExp : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ExpProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcMo : Janus.Contracts.EqHashModel.CodeIn64 Fv256.MulOverflowProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem dsExp : ∀ d ∈ Fv256.ExpProg.program.data, d ∈ Extracted.program.data := by decide

/-- `IndexByteString` (`hibs`) -/
theorem disch_ibs (impl : List Janus.Amd64.Segment) :
    Fv256.IndexByte.IbsLibA (Extracted.program.link impl) ibsEntry avxAddr := by
  intro p n c
  exact Fv256.CodeIn.lib_summary_link impl hcIbs (Fv256.IndexByte.ibs_summary_A p n c)

/-- a library summary, strengthened by a frame fact that holds along every run of the library program -/
theorem strengthen {p : Janus.Amd64.Program} {entry : Nat} {pre : State → Prop} {post : State → State → Prop}
    (hsum : Summary p entry pre post) (F : State → State → Prop)
    (hF : ∀ {s s' : State} {k : Nat}, Janus.Amd64.Program.Steps p s k s' → F s s') :
    Summary p entry pre (fun s s' => post s s' ∧ F s s') := by
  intro s hpc hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hpc hp
  exact ⟨k, s', hst, hr, hq, hF hst⟩

set_option maxRecDepth 100000 in
/-- `Exp` (`hexp`) -/
theorem disch_exp (impl : List Janus.Amd64.Segment) : ExpSumm (Extracted.program.link impl) := by
  have h := Fv256.CodeIn.lib_summary_link impl hcExp
    (strengthen Fv256.Amd64.ExpMain.exp_summary (fun s s' => s'.fsBase = s.fsBase)
      (fun hst => Fv256.FrameFsDf.Steps_fs hst))
  intro s hpc hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hdl⟩ := hp
  obtain ⟨k, s', hst, hr, hq, hfs⟩ := h s hpc
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, Fv256.LinkEq.DataLoaded.of_subset dsExp hdl⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hq
  exact ⟨k, s', hst, hr, q1, q2, q3, q4, q5, q6, q7, q8, q9, hfs⟩

set_option maxRecDepth 100000 in
/-- `MulOverflow` (`hmo`) -/
theorem disch_mo (impl : List Janus.Amd64.Segment) (z x y : BitVec 64) : MoSumm (Extracted.program.link impl) z x y := by
  have h := Fv256.CodeIn.lib_summary_link impl hcMo
    (strengthen (Fv256.Amd64.MoLib.mo_summary z x y) (fun s s' => s'.fsBase = s.fsBase)
      (fun hst => Fv256.FrameFsDf.Steps_fs hst))
  intro s hpc hp
  obtain ⟨k, s', hst, hr, ⟨hq1, hq2, hq3, hq4, hq5, hdf⟩, hfs⟩ := h s hpc hp
  exact ⟨k, s', hst, hr, ⟨hq1, hq2, hq3, hq4, hq5⟩, hfs, hdf⟩

set_option maxRecDepth 100000 in
/-- the SetFromDecimal library program (`Fv256.Amd64.SfdProg`, proved Extracted-free in `SfdLib`) is part of the Scan extraction -/
theorem hLibSfd : Fv256.LinkEq.LibIn Fv256.Amd64.SfdProg.program Extracted.program :=
  Fv256.Amd64.SfdLink.hLib_of_decide (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcaSfd : Fv256.Amd64.SfdLib.ContractsAgree Extracted.program :=
  Fv256.Amd64.SfdLink.hca_of_decide (by decide)

set_option maxRecDepth 100000 in
theorem cfg_eq_ext : cfg = Fv256.Amd64.SfdTopCfg.extCfg := by rfl

set_option maxRecDepth 100000 in
theorem sfdEntry_eq : sfdEntry = Fv256.Amd64.SfdProg.sfd := by decide

/-- the `SetFromDecimal` summary at its entry in the Scan program (`hsfd`): `SfdLib.hsfd_of_link` -/
theorem disch_sfd (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T : Nat)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS' := by
  intro b' L' lo' hi' z pS' nS'
  have h := Fv256.Amd64.SfdLib.hsfd_of_link hLibSfd hcaSfd impl R R2 T hif hnew hmg hmv hwb1 hwb2 hcmp b' L' lo' hi' z pS' nS'
  rw [cfg_eq_ext, sfdEntry_eq]; exact h

end Fv256.Amd64.ScanDisch
