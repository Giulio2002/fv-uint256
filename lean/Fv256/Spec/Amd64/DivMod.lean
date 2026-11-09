import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.DivMod

/-- The address of `uint256.Int`'s type descriptor (the `LEA` before the call loads it): the extraction's only data object. -/
def intType : Nat := Extracted.dataAddr.«type:uint256.Int#33f34945»

end Fv256.Amd64.DivMod
