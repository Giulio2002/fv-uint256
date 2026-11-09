import Extracted
import Fv256.Spec.C
import Fv256.Spec.Core
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.Util

/-! SPECIFICATION part (generated): the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

export Fv256.IntoBig (BigOut BigObj)

/-- IntoBig's entry in Format's extraction (a definition, like `Extracted.entry`, so that offsets stay symbolic) -/
def ibEntry : Nat := 0xb5780

def nm : String := "github.com/holiman/uint256.(*Int).IntoBig"

/-- The type descriptor of `big.Int` passed to `newobject` (`ADRP`+`ADD` at `IntoBig+0x2c`). -/
def bigType : Nat :=
  adrpLdTarget (Fv256.Arm64.IntoBig.ibEntry + 0x2c) (segWord Extracted.program nm 11) (segWord Extracted.program nm 12) 0

/-- The type descriptor of `[4]big.Word` (`ADRP`+`ADD` at `IntoBig+0xa0`). -/
def arrType : Nat :=
  adrpLdTarget (Fv256.Arm64.IntoBig.ibEntry + 0xa0) (segWord Extracted.program nm 40) (segWord Extracted.program nm 41) 0

/-- The address of the write-barrier flag `runtime.writeBarrier` (`ADRP`+`LDR W` at `IntoBig+0x38`). -/
def flagAddr : Nat :=
  adrpLdTarget (Fv256.Arm64.IntoBig.ibEntry + 0x38) (segWord Extracted.program nm 14) (segWord Extracted.program nm 15) 2

end Fv256.Arm64.IntoBig

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
