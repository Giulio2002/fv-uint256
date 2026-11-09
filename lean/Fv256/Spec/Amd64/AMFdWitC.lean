import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Amd64.MustFromDecimal

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.FromDecimalSpec Fv256.Amd64.MustFromDecimal

namespace Fv256.Amd64.MFdWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy

/-- pins the type of an existential variable of `nonvacuous` -/
def pinPanicRuntime (_k : Janus.Spec.PanicRuntime) : Prop := True

open Fv256.CallSites

end Fv256.Amd64.MFdWit
