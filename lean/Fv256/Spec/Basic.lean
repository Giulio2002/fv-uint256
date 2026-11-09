/-!
# Basics shared by every specification in `Fv256/Spec/`

Pure mathematics over `Nat`: no machine, no memory, no registers. A `uint256.Int` is a number in `[0, 2^256)`; each
function specification below says which number (or which error) a call produces from the numbers it is given.
-/

namespace Fv256.Spec

/-- The modulus of 256-bit words: every `uint256.Int` value lies in `[0, W)`, and arithmetic that overflows wraps modulo `W`.
(Specifications write `2 ^ 256` explicitly; this name exists for the proofs.) -/
abbrev W : Nat := 2 ^ 256

/-- A 256-bit word: a natural number below `2^256`. -/
def IsU256 (x : Nat) : Prop := x < 2 ^ 256

end Fv256.Spec
