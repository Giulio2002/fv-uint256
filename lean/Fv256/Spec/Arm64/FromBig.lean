import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.FromBig

def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.FromBig" 8)
    (segWord Extracted.program "github.com/holiman/uint256.FromBig" 9) 0

namespace Witness

open Janus.Contracts.IfaceModel

/-- pins the type of an existential variable of `nonvacuous` -/
def pinBitVec64 (_k : BitVec 64) : Prop := True

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/FromBig.lean

end Witness

end Fv256.Arm64.FromBig
