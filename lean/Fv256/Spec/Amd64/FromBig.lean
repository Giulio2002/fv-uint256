import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.SumC64
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.FromBig

def intType : Nat := dataBase Extracted.program 0

namespace Witness

open Janus.Contracts.AllocSatAmd64 (ret_of)

open Janus.Contracts.AllocSat (le_blockSize)

/-- pins the type of an existential variable of `nonvacuous` -/
def pinBitVec64 (_k : BitVec 64) : Prop := True

open Fv256.CallSites

end Witness

end Fv256.Amd64.FromBig
