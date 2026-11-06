/-!
# Shared specification of the `Reciprocal` value (pure `Nat`, no dependencies)

`recipExact m = ⌊(2^512 - 1) / m⌋`; `RecipOK m mu`: `mu` is `recipExact m` or one less (finding F-F1).  Used by `Reciprocal` (FV-B),
`MulMod`, `MulModWithReciprocal` and `reduce4` (FV-F).
-/

namespace Fv256.F

/-- The exact quantity a 320-bit reciprocal of `m` approximates: `⌊(2^512 - 1) / m⌋`. -/
def recipExact (m : Nat) : Nat := (2 ^ 512 - 1) / m

/-- `mu` is a valid `Reciprocal(m)` value for `2^192 ≤ m < 2^256`: it is `⌊(2^512-1)/m⌋`, or one less
(the Newton refinement of the library may end one unit low). -/
def RecipOK (m mu : Nat) : Prop := recipExact m - 1 ≤ mu ∧ mu ≤ recipExact m

/-- the weaker window provable for every `m` with `2^192 ≤ m` (`ex - 3 ≤ mu ≤ ex`); `MulModWithReciprocal` is specified under this one -/
def RecipWeak (m mu : Nat) : Prop := recipExact m - 3 ≤ mu ∧ mu ≤ recipExact m

theorem RecipOK.weak {m mu : Nat} (h : RecipOK m mu) : RecipWeak m mu := ⟨by have := h.1; omega, h.2⟩

end Fv256.F
