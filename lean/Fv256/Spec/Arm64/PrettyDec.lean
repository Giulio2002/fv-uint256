import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.PrettyMath
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.E
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts

open Fv256.E

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.PrettyDec

/-- the address of `runtime.slicebytetostring` in the extracted program -/
abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

end Fv256.Arm64.PrettyDec
