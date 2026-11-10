import Extracted

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.Amd64.SetBytes

/-- number of bytes used: all of them up to 32, else the last 32 -/
def used (len : Nat) : Nat := if len < 32 then len else 32

end Fv256.Amd64.SetBytes
