import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.PrettyMath
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.E
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

open Fv256.E

namespace Fv256.Amd64.PrettyDec

/-- the address of `runtime.slicebytetostring` in the extracted program -/
abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

end Fv256.Amd64.PrettyDec
