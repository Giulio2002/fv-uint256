import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.SetFromHexLoops
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Fv256.C Fv256.Arm64.SetFromHexLoops

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.FromHex

/-- the type descriptor `FromHex` passes to `runtime.newobject` (`uint256.Int`), recomputed from the extracted words. -/
def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.FromHex" 8)
    (segWord Extracted.program "github.com/holiman/uint256.FromHex" 9) 0

end Fv256.Arm64.FromHex
