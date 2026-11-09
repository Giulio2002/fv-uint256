import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.Clone

/-- The address of `uint256.Int`'s type descriptor (the `LEA` before the call loads it): the extraction's only data object. -/
def intType : Nat := dataBase Extracted.program 0

end Fv256.Amd64.Clone
