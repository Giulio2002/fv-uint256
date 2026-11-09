import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.E

/-- The three digits of `n % 1000`, zero padded. -/
def pad3 (n : Nat) : List Nat := [48 + n / 100 % 10, 48 + n / 10 % 10, 48 + n % 10]

/-- The decimal digits of `n` with `sep` between every group of three digits, counted from the right:
a number below `1000` is its digits; otherwise the grouped digits of `n / 1000`, then `sep`, then the three digits of `n % 1000`. -/
def prettyBytes (sep : Nat) (n : Nat) : List Nat :=
  if h : n < 1000 then decBytes n else prettyBytes sep (n / 1000) ++ sep :: pad3 (n % 1000)
termination_by n
decreasing_by omega

/-- The number of output bytes. -/
def plen (v : Nat) : Nat := decLen v + (decLen v - 1) / 3
