import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.PaddedBytes

/-- the type descriptor of `uint8` passed to `runtime.makeslice` (the `LEA` before the call): the extraction's only data object. -/
def byteType : Nat := dataBase Extracted.program 0

end Fv256.Amd64.PaddedBytes
