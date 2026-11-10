import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.DivMod

def intType : Nat := Extracted.dataAddr.«type:uint256.Int#33f34945»

end Fv256.Arm64.DivMod
