import Extracted
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.PaddedBytes

/-- the type descriptor of `uint8` passed to `runtime.makeslice` (the `LEA` before the call): the extraction's only data object. -/
def byteType : Nat := dataBase Extracted.program 0

end Fv256.Amd64.PaddedBytes
