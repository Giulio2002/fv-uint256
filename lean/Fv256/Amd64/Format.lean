import Extracted
import Fv256.SpecFormat

/-!
# `(*uint256.Int).Format(s fmt.State, ch rune)` (amd64) -- STATEMENT PROBE (audit verdict), placeholder post

Callees as hypotheses, all `ICallContract64` (Go ABI only, `Janus.Contracts.ICall`): the four `fmt.State` methods through the itab
(`fn` variables), and the two static callees `fmt.Fprint`, `math/big.(*Int).Format` at `contractAddr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.ICall Janus.Spec.Type Janus.Contracts.IfaceAmd64

namespace Fv256.Amd64.Format

theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : Janus.Contracts.RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (fW fP fF fWr stack : Nat) (rt : List (Nat × Nat)) (RW RP RF RWr RFp RBf : Res)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True))
    (hP : ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True))
    (hF : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True))
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr (fun _ => True))
    (hFp : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => []) RFp (fun _ => True))
    (hBf : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 80 rt (fun _ => []) RBf (fun _ => True))
    (z tab data ch : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, data, ch]
      (fun s => CallerOK R s 72 8)
      (fun s s' => s'.regs 14 = s.regs 14) := by
  sorry

end Fv256.Amd64.Format
