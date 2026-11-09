import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.NewInt

/-- The address of `uint256.Int`'s type descriptor, the argument `NewInt` passes to `runtime.newobject`
(the `ADRP` + `ADD` pair at `NewInt+0x1c`), recomputed from the extracted words. -/
def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "github.com/holiman/uint256.NewInt" 7)
    (segWord Extracted.program "github.com/holiman/uint256.NewInt" 8) 0

end Fv256.Arm64.NewInt
