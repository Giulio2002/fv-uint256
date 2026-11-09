import Extracted
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ExtendSign

/-- equal or disjoint 32-byte objects -/
def Alias (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32

end Fv256.Amd64.ExtendSign
