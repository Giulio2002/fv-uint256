import Extracted
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.PaddedBytes

/-- the type descriptor of `uint8` passed to `runtime.makeslice` (ADRP + ADD at entry+0x20). -/
def byteType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.(*Int).PaddedBytes" 8)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).PaddedBytes" 9) 0

end Fv256.Arm64.PaddedBytes
