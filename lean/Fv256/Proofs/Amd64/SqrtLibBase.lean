import Janus
import Fv256.Proofs.Common.SqrtProg

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SqrtLib

/-- entry of `(*Int).Sqrt` in the library program -/
abbrev sqrtEntry : Nat := segAddr Fv256.SqrtProg.program "github.com/holiman/uint256.(*Int).Sqrt"

end Fv256.Amd64.SqrtLib
