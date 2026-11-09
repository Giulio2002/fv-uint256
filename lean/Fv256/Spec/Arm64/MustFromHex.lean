import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.SetFromHexLoops
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic Fv256.C Fv256.Arm64.SetFromHexLoops

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MustFromHex

/-- the type descriptor `FromHex` passes to `runtime.newobject` (`uint256.Int`), recomputed from the extracted words. -/
def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.MustFromHex" 8)
    (segWord Extracted.program "github.com/holiman/uint256.MustFromHex" 9) 0

namespace Witness

open Janus.Contracts.IfaceModel

/-- pins the type of an existential variable of `nonvacuous` -/
def pinPanicRuntime (_k : PanicRuntime) : Prop := True

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/MustFromHex.lean

end Witness

end Fv256.Arm64.MustFromHex
