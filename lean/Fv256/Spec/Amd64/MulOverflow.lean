import Extracted
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulOverflow

def Alias (p q : BitVec 64) : Prop := p = q ∨ p.toNat + 32 ≤ q.toNat ∨ q.toNat + 32 ≤ p.toNat

end Fv256.Amd64.MulOverflow
