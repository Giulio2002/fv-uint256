

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.F

/-- The exact quantity a 320-bit reciprocal of `m` approximates: `⌊(2^512 - 1) / m⌋`. -/
def recipExact (m : Nat) : Nat := (2 ^ 512 - 1) / m

/-- `mu` is a valid `Reciprocal(m)` value for `2^192 ≤ m < 2^256`: it is `⌊(2^512-1)/m⌋`, or one less
(the Newton refinement of the library may end one unit low). -/
def RecipOK (m mu : Nat) : Prop := recipExact m - 1 ≤ mu ∧ mu ≤ recipExact m

/-- the weaker window provable for every `m` with `2^192 ≤ m` (`ex - 3 ≤ mu ≤ ex`); `MulModWithReciprocal` is specified under this one -/
def RecipWeak (m mu : Nat) : Prop := recipExact m - 3 ≤ mu ∧ mu ≤ recipExact m

end Fv256.F
