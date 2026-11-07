import Fv256.LinkEq
import Fv256.Amd64.SfdTopI

/-!
# `SetFromDecimal` (amd64): the library lemma for consumers (Extracted-free)

`Fv256.Amd64.SfdTop.sfd_sum` is proved once over the library program `Fv256.Amd64.SfdProg.program` (this module and everything it
imports is independent of any extraction, so consumers reuse the compiled proof).  `hsfd_of_link` moves it to a consumer's extracted
program `E`: `LibIn SfdProg.program E` (the library segments / stubs / exit address are those of `E`, its segments are pairwise
disjoint; the consumer checks it by `decide`, see `Fv256.Amd64.SfdLink.hLib_of_decide`), the contract addresses agree, and the six runtime
contracts are hypotheses about the REAL program `E.link impl`.  They are moved to the library program linked with the consumer's
remaining code (`rest ++ impl`) by `ProgEq`, `sfd_sum` is applied there, and the summary moves back.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg

namespace Fv256.Amd64.SfdLib

/-- the runtime contracts `hsfd_of_link` uses -/
def contractNames : List String :=
  ["runtime.ifaceeq", "runtime.newobject", "runtime.mallocgc", "runtime.memmove", "runtime.gcWriteBarrier1",
   "runtime.gcWriteBarrier2", "runtime.cmpstring"]

/-- the consumer's contract addresses are the library's -/
def ContractsAgree (E : Janus.Amd64.Program) : Prop :=
  ∀ n ∈ contractNames, E.contractAddr n = Fv256.Amd64.SfdProg.program.contractAddr n

theorem hsfd_of_link {E : Janus.Amd64.Program} (hE : Fv256.LinkEq.LibIn Fv256.Amd64.SfdProg.program E)
    (hca : ContractsAgree E) (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T : Nat)
    (hif : Ifaceeq (E.link impl) (E.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (E.link impl) (E.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (E.link impl) (E.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (E.link impl) (E.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (E.link impl) (E.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (E.link impl) (E.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (E.link impl) (E.contractAddr "runtime.cmpstring") 16) :
    ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary extCfg (E.link impl) Fv256.Amd64.SfdProg.sfd R R2 T b' L' lo' hi' z pS' nS' := by
  intro b' L' lo' hi' z pS' nS'
  have hP := hE.progEq impl
  rw [hca "runtime.ifaceeq" (by simp [contractNames])] at hif
  rw [hca "runtime.newobject" (by simp [contractNames])] at hnew
  rw [hca "runtime.mallocgc" (by simp [contractNames])] at hmg
  rw [hca "runtime.memmove" (by simp [contractNames])] at hmv
  rw [hca "runtime.gcWriteBarrier1" (by simp [contractNames])] at hwb1
  rw [hca "runtime.gcWriteBarrier2" (by simp [contractNames])] at hwb2
  rw [hca "runtime.cmpstring" (by simp [contractNames])] at hcmp
  exact Fv256.LinkEq.Summary.of_progEq hP
    (Fv256.Amd64.SfdTop.sfd_sum (Fv256.LinkEq.rest Fv256.Amd64.SfdProg.program E ++ impl) R R2 T b' L' lo' hi' z pS' nS'
      (Fv256.LinkEq.Summary.of_progEq hP.symm hif)
      (fun L b => Fv256.LinkEq.Summary.of_progEq hP.symm (hnew L b))
      (fun L b => Fv256.LinkEq.Summary.of_progEq hP.symm (hmg L b))
      (fun L b => Fv256.LinkEq.Summary.of_progEq hP.symm (hmv L b))
      (fun L b => Fv256.LinkEq.Summary.of_progEq hP.symm (hwb1 L b))
      (fun L b => Fv256.LinkEq.Summary.of_progEq hP.symm (hwb2 L b))
      (Fv256.LinkEq.Summary.of_progEq hP.symm hcmp))

end Fv256.Amd64.SfdLib
