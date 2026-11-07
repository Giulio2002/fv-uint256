import Extracted
import Fv256.Amd64.SfdTopI
import Fv256.Amd64.SummaryEnsures

/-!
# `(*uint256.Int).SetFromDecimal(s string) error` (amd64): the Extracted-level theorem

The statement is `Fv256.Amd64.SfdTopSpec.TopPre/TopPost` instantiated with the addresses of THIS extraction (`extCfg`: every
field is an `Extracted.dataAddr` / `contractAddr`).  The runtime contracts are hypotheses about the runtime's own code
`Extracted.program.ofImpl impl` (`ImplApart Extracted.program impl` is the one premise on `impl`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Janus.Contracts.EqHashModel Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg

namespace Fv256.Amd64.SetFromDecimal

set_option maxRecDepth 100000 in
theorem entry_eq : Extracted.entry = Fv256.Amd64.SfdTop.sfd := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hI : Amd64.ImplApart Extracted.program impl)
    (hif : Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pS, nS]
      (fun s => TopPre extCfg R R2 T b L lo hi z pS nS s)
      (fun s s' => TopPost extCfg R R2 T b L lo hi z pS nS s s') := by
  have hc := codeIn_ofImpl_of_apart64 hI
  have hif' := Summary.of_codeIn64 hc hif
  have hnew' := NewobjectLiveContract64.of_codeIn hc hnew
  have hmg' := MallocgcLiveContract64.of_codeIn hc hmg
  have hmv' := MemmoveLive64.of_codeIn hc hmv
  have hwb1' := WbLiveContract64.of_codeIn hc hwb1
  have hwb2' := WbLiveContract64.of_codeIn hc hwb2
  have hcmp' := Summary.of_codeIn64 hc hcmp
  rw [entry_eq]
  exact Fv256.Amd64.SummaryEnsures.ensures_of_summary64
    (Fv256.Amd64.SfdTop.sfd_sum impl R R2 T b L lo hi z pS nS hif' hnew' hmg' hmv' hwb1' hwb2' hcmp')
    (fun ret s hret hs hp => hp)
    (fun ret s s' hret hs hp hq => ⟨⟨hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1⟩, hq⟩)

end Fv256.Amd64.SetFromDecimal
