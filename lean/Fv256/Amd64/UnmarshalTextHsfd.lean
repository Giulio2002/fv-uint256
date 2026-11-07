import Extracted
import Fv256.Amd64.UnmarshalText

/-!
# `UnmarshalText` (amd64): the `SetFromDecimal` summary `hsfd` from the library lemma (discharge, one small lemma per function)

PENDING: `Fv256.Amd64.SfdLib.hsfd_of_link` (FV-I5, planned statement in /srv/fv-uint256-wi/NOTES-I.md).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib
open Fv256.Amd64.UnmarshalTextS

namespace Fv256.Amd64.UnmarshalTextHsfd

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
  sorry -- PENDING hsfd_of_link

end Fv256.Amd64.UnmarshalTextHsfd
