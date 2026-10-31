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

/-- `z.And(x, y)`: bitwise and of the two numbers. -/
def and (x y : Nat) : Nat := x &&& y
/-- `z.Or(x, y)`. -/
def or (x y : Nat) : Nat := x ||| y
/-- `z.Xor(x, y)`. -/
def xor (x y : Nat) : Nat := x ^^^ y

/-- `z.Eq(x)`. -/
def eq (x y : Nat) : Bool := x == y
/-- `z.Lt(x)`: unsigned less-than. -/
def lt (x y : Nat) : Bool := decide (x < y)
/-- `z.Gt(x)`: unsigned greater-than. -/
def gt (x y : Nat) : Bool := decide (y < x)
/-- `z.Cmp(x)`: -1, 0 or 1. -/
def cmp (x y : Nat) : Int := if x < y then -1 else if x = y then 0 else 1

/-- `z.Not(x)`: bitwise complement of a 256-bit number. -/
def not (x : Nat) : Nat := W - 1 - x
/-- `z.Neg(x)`: two's complement negation modulo `2^256`. -/
def neg (x : Nat) : Nat := (W - x) % W
/-- `z.Add(x, y)`. -/
def add (x y : Nat) : Nat := (x + y) % W
/-- `z.Sub(x, y)`. -/
def sub (x y : Nat) : Nat := (x + W - y) % W
/-- `z.Mul(x, y)`. -/
def mul (x y : Nat) : Nat := (x * y) % W

end Fv256.Spec
