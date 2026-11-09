import Extracted
import Janus.Contracts.IfaceLive
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.DecExt
import Fv256.Spec.DecAt
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.E
import Fv256.Spec.Txt
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts

open Fv256.E

open Fv256.Arm64.Dec

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Value

abbrev cvAddr : Nat := Extracted.program.contractAddr "runtime.convTstring"

/-- the readiness the live `slicebytetostring` contract needs at `Dec`'s single call: for every memory the runtime sees as `v`, the request is
served, the runtime invariant holds for some live set and a budget that covers the request and the `convTstring` request that follows
(16 bytes), and the call window is apart from the live set and the runtime ranges.  (The stack check is not part of it: it depends on memory
outside the runtime's view and is the `GuardOK` of the precondition.) -/
def HL (R : RtInv) : RtReady := fun a g sp v => ∀ m, rtView R.rt m = v →
  ∃ (L : List (Nat × Nat)) (b : Nat), LiveAt R ssAddr a L b (slicebytetostringLive.cost a m + 16) g m (windowAt sp 4096 3)

end Fv256.Arm64.Value
