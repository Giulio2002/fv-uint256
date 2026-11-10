import Extracted
import Janus.Contracts.IfaceLive
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Amd64.DecExt
import Fv256.Spec.Amd64.SbtsG
import Fv256.Spec.DecAt
import Fv256.Spec.Core
import Fv256.Spec.E
import Fv256.Spec.PrettyMath
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

open Fv256.E

open Fv256.Amd64.Dec

open Fv256.Amd64.SbtsG

namespace Fv256.Amd64.Value

abbrev cvAddr : Nat := Extracted.program.contractAddr "runtime.convTstring"

/-- the readiness the live `slicebytetostring` contract needs at `Dec`'s single call (see `Fv256.Arm64.Value.HL`; the stack check is the
`StackGuardOK` of the precondition) -/
def HL (R : RtInv) : RtReady := fun a g sp v => ∀ m, rtView R.rt m = v →
  ∃ (L : List (Nat × Nat)) (b : Nat), LiveAt R ssAddr a L b (slicebytetostringLive.cost a m + 16) g m (window64 sp 4096 3)

end Fv256.Amd64.Value
