import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.MustFromDecimal

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.FromDecimalSpec Fv256.Arm64.MustFromDecimal

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MFdWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy

/-- pins the type of an existential variable of `nonvacuous` -/
def pinPanicRuntime (_k : Janus.Spec.PanicRuntime) : Prop := True

-- CALLSITE-LIVE-BLOCK

end Fv256.Arm64.MFdWit
