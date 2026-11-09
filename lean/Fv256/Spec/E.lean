

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.E

/-- The ASCII bytes of the base-10 representation of `n`, most significant digit first, without
leading zeros (`0` is `"0"`). -/
def decBytes (n : Nat) : List Nat :=
  if h : n < 10 then [48 + n] else decBytes (n / 10) ++ [48 + n % 10]
termination_by n
decreasing_by omega

/-- The number of decimal digits of `n` (`1` for `0`). -/
def decLen (n : Nat) : Nat := (decBytes n).length

end Fv256.E
