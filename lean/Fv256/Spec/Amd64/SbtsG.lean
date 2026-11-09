import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.SbtsG

/-- The window of an amd64 call with `stack` bytes below `RSP` and `nargs` argument words above the return address. -/
def window64 (sp stack nargs : Nat) : List (Nat × Nat) := [(sp - stack, sp), (sp + 8, sp + 8 + 8 * nargs), (sp, sp + 8)]

end Fv256.Amd64.SbtsG
