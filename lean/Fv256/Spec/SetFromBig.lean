import Fv256.Spec.BigInt

/-!
# `func (z *Int) SetFromBig(b *big.Int) bool`

`z.SetFromBig(b)` sets `z` to the integer `b` modulo `2^256` (two's complement: a negative `b` wraps, `-1` becomes `2^256 - 1`) and
returns whether `b` was too big: `true` iff the magnitude of `b` has MORE THAN FOUR 64-bit limbs. (Only the low four limbs are read, so on
overflow `z` is the low 256 bits of `|b|`, negated when `b < 0`; this is again `b mod 2^256`.) `b` must not be nil.
-/

namespace Fv256.Spec

/-- The number `z` holds after `z.SetFromBig(b)` for the integer value `b`: `b mod 2^256` (a negative `b` wraps around). -/
def setFromBig (b : Int) : Nat := (b % 2 ^ 256).toNat

/-- The boolean `z.SetFromBig(b)` returns, for a `b` whose magnitude has `limbs` 64-bit limbs: more than `256/64 = 4` limbs. -/
def setFromBigOverflow (limbs : Nat) : Bool := decide (4 < limbs)

/-- Small numbers are kept. -/
example : setFromBig 5 = 5 := by decide

/-- `-1` wraps to the largest word. -/
example : setFromBig (-1) = 2 ^ 256 - 1 := by decide

/-- `2^256` wraps to zero. -/
example : setFromBig (2 ^ 256) = 0 := by decide

/-- Four limbs fit, five overflow. -/
example : setFromBigOverflow 4 = false ∧ setFromBigOverflow 5 = true := by decide

end Fv256.Spec
