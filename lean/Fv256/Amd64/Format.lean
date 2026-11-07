import Extracted
import Fv256.SpecFormat

/-!
# `(*uint256.Int).Format(s fmt.State, ch rune)` (amd64) -- UNION PROBE (statement audit, sorry proof, placeholder post)

Runtime hypotheses of all paths in one statement: the interface model `R` with `TypeAssert` (nil path), the allocator `R2 : RtInv`
with the live `newobject` / write-barrier contracts (big path, `IntoBig`), the ready runtime `H` with `RtContract64` for
`slicebytetostring` / `stringtoslicebyte` (fast path), and the callee hypotheses (`ICallContract64`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel
open Janus.Spec.Type (IfaceModel)

namespace Fv256.Amd64.Format

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

theorem correctness (impl : List Janus.Amd64.Segment) (hI : ImplApart Extracted.program impl)
    (R : IfaceModel) (hl : R.Laws) (H : Janus.Contracts.RtReady)
    (hta : Janus.Contracts.IfaceAmd64.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (R2 : RtInv)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R2)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2)
    (rt : List (Nat × Nat))
    (hss : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hst : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (fW fP fF fWr stack : Nat) (RW RP RF RWr RFp RBf : Res)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True))
    (hP : ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True))
    (hF : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True))
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr (fun _ => True))
    (hFp : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => []) RFp (fun _ => True))
    (hBf : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 80 rt (fun _ => []) RBf (fun _ => True))
    (z tab data ch : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, data, ch]
      (fun s => (s.regs 4).toNat % 8 = 0)
      (fun s s' => s'.regs 14 = s.regs 14) := by
  sorry

end Fv256.Amd64.Format
