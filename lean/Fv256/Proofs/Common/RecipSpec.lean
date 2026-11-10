import Fv256.Proofs.Legacy.RecipSpec


/-!
# Shared specification of the `Reciprocal` value (pure `Nat`, no dependencies)

`recipExact m = ⌊(2^512 - 1) / m⌋`; `RecipOK m mu`: `mu` is `recipExact m` or one less (finding F-F1).  Used by `Reciprocal` (FV-B),
`MulMod`, `MulModWithReciprocal` and `reduce4` (FV-F).
-/

namespace Fv256.F

theorem RecipOK.weak {m mu : Nat} (h : RecipOK m mu) : RecipWeak m mu := ⟨by have := h.1; omega, h.2⟩

end Fv256.F
