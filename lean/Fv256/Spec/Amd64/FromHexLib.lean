import Fv256.Spec.HexLemmas
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.SumC64
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.C

namespace Fv256.Amd64.FromHexLib

/-- the address of the package variable (an `error` interface value) for each parse error tag -/
def errAddrOf (e : Nat) : Nat :=
  if e = 0 then 5995344 else if e = 1 then 5995376 else if e = 2 then 5995392
  else if e = 3 then 5995408 else if e = 4 then 5995424 else 5995360

end Fv256.Amd64.FromHexLib
