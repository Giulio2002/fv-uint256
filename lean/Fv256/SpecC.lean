import Fv256.Spec

/-!
# Independent specification, family C (conversion, parsing, encoding)

Plain mathematical models, written without reference to the Go code.
-/

namespace Fv256.C

open Fv256.Spec

/-- The natural number whose `n` little-endian 64-bit words are `w 0, w 1, ..., w (n-1)`
(word `i` has weight `2^(64 i)`): the magnitude of a `big.Int` with `n` words. -/
def bigAbs (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bigAbs w n + w n * 2 ^ (64 * n)

/-- `z.SetFromBig(b)`: the value stored in `z` for a `big.Int` of sign `neg` and magnitude `abs`:
the magnitude reduced modulo `2^256`, negated modulo `2^256` when `neg`. -/
def fromBig (neg : Bool) (abs : Nat) : Nat := if neg then Spec.neg (abs % W) else abs % W

/-- `z.SetFromBig(b)` overflow flag: the magnitude has more than `256/64 = 4` words. -/
def fromBigOv (len : Nat) : Bool := decide (4 < len)

end Fv256.C
