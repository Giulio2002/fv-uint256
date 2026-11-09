import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZ

/-- the type descriptor of `uint8` passed to `runtime.makeslice` (ADRP + ADD at entry+0x1c). -/
def byteType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).MarshalSSZ" 7)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).MarshalSSZ" 8) 0

end Fv256.Arm64.MarshalSSZ
