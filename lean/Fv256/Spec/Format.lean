import Fv256.Spec.C
import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.FormatSpec

/-- lowercase hexadecimal digits of `n` (ASCII), most significant first, no prefix, no leading zeros; `0` is `"0"` -/
def hexBytes (n : Nat) : List Nat :=
  if h : n < 16 then [if n < 10 then 48 + n else 87 + n] else hexBytes (n / 16) ++ [if n % 16 < 10 then 48 + n % 16 else 87 + n % 16]
termination_by n
decreasing_by omega

/-- the bytes the fast path writes -/
def fastBytes (z ch : Nat) : List Nat := if ch = 120 then hexBytes z else Fv256.E.decBytes z

/-- `"<nil>"` -/
def nilText : List Nat := [60, 110, 105, 108, 62]

end Fv256.FormatSpec
