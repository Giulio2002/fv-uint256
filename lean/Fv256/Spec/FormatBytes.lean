import Fv256.Spec.C
import Fv256.Spec.E

/-! Implementation-shaped byte lists used by the machine-level proofs of `Format` (`Fv256.FormatSpec`). The readable specification of `Format` is `Fv256/Spec/Format.lean`; `Proofs/Common/FormatBridge.lean` proves that these agree with it. -/


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
