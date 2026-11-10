import Extracted
import Fv256.Spec.DecAt
import Fv256.Spec.Core
import Fv256.Spec.E
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts

open Fv256.E

namespace Fv256.Arm64.Dec

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

end Fv256.Arm64.Dec
