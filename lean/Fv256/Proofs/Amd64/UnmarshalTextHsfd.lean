import Extracted
import Fv256.Proofs.Amd64.SfdLink
import Fv256.Proofs.Amd64.UnmarshalText

/-!
# `UnmarshalText` (amd64): the `SetFromDecimal` summary `hsfd` from the library lemma (discharge, one small lemma per function)

Discharged by `Fv256.Amd64.SfdLib.hsfd_of_link` (FV-I7), via hLib/hca by `decide` against this extraction.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib
open Fv256.Amd64.UnmarshalTextS

namespace Fv256.Amd64.UnmarshalTextHsfd

set_option maxRecDepth 100000 in
theorem hLib : Fv256.LinkEq.LibIn Fv256.Amd64.SfdProg.program Extracted.program :=
  Fv256.Amd64.SfdLink.hLib_of_decide (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hca : Fv256.Amd64.SfdLib.ContractsAgree Extracted.program :=
  Fv256.Amd64.SfdLink.hca_of_decide (by decide)

set_option maxRecDepth 100000 in
theorem cfg_eq : Fv256.Amd64.UnmarshalTextS.cfg = Fv256.Amd64.SfdTopCfg.extCfg := by
  unfold Fv256.Amd64.UnmarshalTextS.cfg Fv256.Amd64.SfdTopCfg.extCfg; rfl

set_option maxRecDepth 100000 in
theorem entry_eq : Fv256.Amd64.UnmarshalTextS.sfdEntry = Fv256.Amd64.SfdProg.sfd := by decide

theorem hsfd (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T : Nat)
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
      SfdSummary Fv256.Amd64.UnmarshalTextS.cfg (Extracted.program.link impl) Fv256.Amd64.UnmarshalTextS.sfdEntry R R2 T b' L' lo' hi' z pS' nS' := by
  intro b' L' lo' hi' z pS' nS'
  rw [cfg_eq, entry_eq]
  exact Fv256.Amd64.SfdLib.hsfd_of_link hLib hca impl R R2 T hif hnew hmg hmv hwb1 hwb2 hcmp b' L' lo' hi' z pS' nS'

end Fv256.Amd64.UnmarshalTextHsfd
