/-!
# The value of a Go `*big.Int`, as the big-integer functions of `uint256` see it

A `big.Int` is a sign flag `neg` and a magnitude `abs`, stored as `n` little-endian 64-bit limbs (`big.Word`s on a 64-bit machine):
`abs = limb 0 + 2^64 * limb 1 + … + 2^(64 (n-1)) * limb (n-1)`. The functions `SetFromBig`, `FromBig`, `MustFromBig` and `CmpBig` read
exactly this; `ToBig` and `IntoBig` build one.
-/

namespace Fv256.Spec

/-- The magnitude of a `big.Int` with `n` limbs `limb 0, …, limb (n-1)`, least significant first: limb `i` has weight `2^(64 i)`. -/
def bigMagnitude (limb : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bigMagnitude limb n + limb n * 2 ^ (64 * n)

/-- The integer value of a `big.Int` with sign flag `neg` (true = negative) and the `n` limbs `limb 0, …, limb (n-1)`. -/
def bigValue (neg : Bool) (limb : Nat → Nat) (n : Nat) : Int :=
  if neg then -(bigMagnitude limb n : Int) else (bigMagnitude limb n : Int)

/-- Two limbs, least significant first. -/
example : bigMagnitude (fun i => [1, 2].getD i 0) 2 = 1 + 2 * 2 ^ 64 := by decide

/-- A negative sign flag negates. -/
example : bigValue true (fun _ => 5) 1 = -5 := by decide

end Fv256.Spec
