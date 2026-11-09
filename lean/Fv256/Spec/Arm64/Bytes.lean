import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Bytes

def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).Bytes" 7)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).Bytes" 8) 0

end Fv256.Arm64.Bytes
