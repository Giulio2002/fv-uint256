import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Fv256.C

namespace Fv256.C

/-- the byte sequence of the string -/
def bytesAt (m : Memory) (hp : Nat) : Nat → Nat := fun k => m.readLE (hp + k) 1

end Fv256.C
