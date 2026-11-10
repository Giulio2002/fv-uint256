import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.HexLemmas
import Janus
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Fv256.C Fv256.Hex

namespace Fv256.Amd64.Hex

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

end Fv256.Amd64.Hex
