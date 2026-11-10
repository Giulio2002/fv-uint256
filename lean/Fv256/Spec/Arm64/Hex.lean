import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.HexLemmas
import Janus
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Fv256.C Fv256.Hex

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Hex

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

end Fv256.Arm64.Hex
