import Janus

/-!
# Independent specification of holiman/uint256

Everything here is a plain mathematical model of 256-bit unsigned arithmetic, written without
reference to the Go code or to any machine: a `uint256.Int` denotes a natural number `x < 2^256`,
and every operation is a function on such numbers (or on `Nat` reduced modulo `2^256`).
The theorem modules relate the compiled machine code to these functions; the only bridge is the
memory layout (`Janus.Spec.val256`: the 32 bytes at the pointer read as one little-endian number,
which is how `[4]uint64` limbs are stored).
-/

namespace Fv256.Spec

/-- The modulus of 256-bit words. -/
abbrev W : Nat := 2 ^ 256

/-- `x.IsZero()`. -/
def isZero (x : Nat) : Bool := x == 0

end Fv256.Spec
