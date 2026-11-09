import Extracted
import Fv256.Spec.C
import Fv256.Spec.Core
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.Util

/-! SPECIFICATION part (generated): the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

export Fv256.IntoBig (BigOut BigObj)

/-- The type descriptor of `big.Int` passed to `newobject` (the RIP-relative `LEAQ` at `IntoBig+0x2b`). -/
def bigType : Nat := ripTarget Extracted.program ((Extracted.entry + 0x60) + 0x2b)

/-- The type descriptor of `[4]big.Word` (the `LEAQ` at `IntoBig+0xa5`). -/
def arrType : Nat := ripTarget Extracted.program ((Extracted.entry + 0x60) + 0xa5)

/-- The address of the write-barrier flag `runtime.writeBarrier` (the `CMPL` at `IntoBig+0x37`). -/
def flagAddr : Nat := ripTarget Extracted.program ((Extracted.entry + 0x60) + 0x37)

end Fv256.Amd64.IntoBig

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
