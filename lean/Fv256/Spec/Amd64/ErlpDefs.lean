import Extracted
import Janus
import Fv256.Spec.Core
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

/-- the type descriptors the two kinds of allocation use (`[33]byte`, then `[1]byte`): inside the extraction's data object -/
def tyBig : Nat := dataBase Extracted.program 0

def tyOne : Nat := dataBase Extracted.program 0 + 0xC0

end Fv256.Amd64.EncodeRLP
