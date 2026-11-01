import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.PaddedBytes

/-- the type descriptor of `uint8` passed to `runtime.makeslice` (ADRP + ADD at entry+0x20). -/
def byteType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.(*Int).PaddedBytes" 8)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).PaddedBytes" 9) 0

end Fv256.Arm64.PaddedBytes
