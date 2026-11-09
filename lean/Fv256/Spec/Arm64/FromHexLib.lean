import Fv256.Spec.HexLemmas
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.C

namespace Fv256.Arm64.FromHexLib

/-- the address of the package variable (an `error` interface value) for each parse error -/
def errAddrOf (e : Nat) : Nat :=
  if e = 0 then 1792784 else if e = 1 then 1792816 else if e = 2 then 1792832
  else if e = 3 then 1792848 else if e = 4 then 1792864 else 1792800

end Fv256.Arm64.FromHexLib
