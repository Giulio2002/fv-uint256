import Extracted
import Fv256.Spec.RlpSpec
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

/-- the type descriptors the two kinds of allocation use (`[33]byte`, then `[1]byte`): the `ADRP`+`ADD` pairs at `+0x9c`, `+0x144` -/
def tyBig : Nat :=
  adrpLdTarget (Extracted.entry + 0x9c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 39)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 40) 0

def tyOne : Nat :=
  adrpLdTarget (Extracted.entry + 0x144) (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 81)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 82) 0

end Fv256.Arm64.EncodeRLP
