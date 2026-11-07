import Extracted
import Fv256.Amd64.SfdTopI
import Fv256.Amd64.SummaryEnsures
import Fv256.Amd64.SfdWitC

/-!
# `(*uint256.Int).SetFromDecimal(s string) error` (amd64): the Extracted-level theorem

The statement is `Fv256.Amd64.SfdTopSpec.TopPre/TopPost` instantiated with the addresses of THIS extraction (`extCfg`: every
field is an `Extracted.dataAddr` / `contractAddr`).  The runtime contracts are hypotheses about the linked program `Extracted.program.link impl`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Janus.Contracts.EqHashModel Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg
  Janus.Contracts.Toy Janus.Contracts.IfaceModel

namespace Fv256.Amd64.SetFromDecimal

set_option maxRecDepth 100000 in
theorem entry_eq : Extracted.entry = Fv256.Amd64.SfdTop.sfd := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pS, nS]
      (fun s => TopPre extCfg R R2 T b L lo hi z pS nS s)
      (fun s s' => TopPost extCfg R R2 T b L lo hi z pS nS s s') := by
  rw [entry_eq]
  exact Fv256.Amd64.SummaryEnsures.ensures_of_summary64
    (Fv256.Amd64.SfdTop.sfd_sum impl R R2 T b L lo hi z pS nS hif hnew hmg hmv hwb1 hwb2 hcmp)
    (fun ret s hret hs hp => hp)
    (fun ret s s' hret hs hp hq => ⟨⟨hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1⟩, hq⟩)

namespace Witness

set_option maxRecDepth 100000 in
/-- The hypotheses of `correctness` hold together: a runtime (`impl`, `R`, `R2`), a budget, a stack window and a call of
`SetFromDecimal(z, "7")` (non-empty input) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pS nS : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pS, nS] s ∧
    TopPre extCfg R R2 T b L lo hi z pS nS s :=
  ⟨implA, R, R0, TD, 0x400, [], loW, hiW, zV, pSV, 1#64, retW, s0,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, hret, setup, pre0⟩

end Witness

end Fv256.Amd64.SetFromDecimal
