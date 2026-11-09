import Janus
import Fv256.Spec.Basic
import Fv256.Spec.Add   -- `Fv256.Spec.add` lives in its own pure file
import Fv256.Spec.IsZero
import Fv256.Spec.Eq
import Fv256.Spec.Lt
import Fv256.Spec.Gt
import Fv256.Spec.Cmp
import Fv256.Spec.Uint64
import Fv256.Spec.IsUint64
import Fv256.Spec.Sign
import Fv256.Spec.Signed
import Fv256.Spec.Slt
import Fv256.Spec.Sgt
import Fv256.Spec.Uint64WithOverflow
import Fv256.Spec.BitLen
import Fv256.Spec.ByteLen
import Fv256.Spec.Byte

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.Spec

/-- `z.And(x, y)`: bitwise and of the two numbers. -/
def and (x y : Nat) : Nat := x &&& y

/-- `z.Or(x, y)`. -/
def or (x y : Nat) : Nat := x ||| y

/-- `z.Xor(x, y)`. -/
def xor (x y : Nat) : Nat := x ^^^ y

/-- `z.Not(x)`: bitwise complement of a 256-bit number. -/
def not (x : Nat) : Nat := W - 1 - x

/-- `z.Neg(x)`: two's complement negation modulo `2^256`. -/
def neg (x : Nat) : Nat := (W - x) % W

/-- `z.Sub(x, y)`. -/
def sub (x y : Nat) : Nat := (x + W - y) % W

/-- `z.Mul(x, y)`. -/
def mul (x y : Nat) : Nat := (x * y) % W

/-- `z.Clear()`. -/
def clear : Nat := 0

/-- `z.SetOne()`. -/
def one : Nat := 1

/-- `z.SetAllOne()`: all 256 bits set. -/
def allOne : Nat := W - 1

/-- `z.Set(x)`. -/
def set (x : Nat) : Nat := x

/-- `z.AddOverflow(x, y)` overflow flag: the true sum does not fit in 256 bits. -/
def addOv (x y : Nat) : Bool := decide (W ≤ x + y)

/-- `z.SubOverflow(x, y)` overflow flag: `x < y`. -/
def subOv (x y : Nat) : Bool := decide (x < y)

/-- `z.AddUint64(x, n)`. -/
def addU (x n : Nat) : Nat := (x + n) % W

/-- `z.SubUint64(x, n)`. -/
def subU (x n : Nat) : Nat := (x + W - n) % W

/-- `z.SetUint64(n)`. -/
def setU (n : Nat) : Nat := n

/-- `z.Abs(x)`: the absolute value of the two's-complement reading, modulo `2^256`. -/
def abs (x : Nat) : Nat := if x < 2 ^ 255 then x else (W - x) % W

/-- `z.Lsh(x, n)`: shift left by `n` bits, modulo `2^256` (zero once `n ≥ 256`). -/
def lsh (x n : Nat) : Nat := (x * 2 ^ n) % W

/-- `z.Rsh(x, n)`: logical shift right by `n` bits (zero once `n ≥ 256`). -/
def rsh (x n : Nat) : Nat := x / 2 ^ n

/-- `z.SRsh(x, n)`: arithmetic shift right of the two's-complement reading of `x` by `n` bits (floor division), as `~(~x >> n)` for negative `x`. -/
def srsh (x n : Nat) : Nat := if x < W / 2 then x / 2 ^ n else W - 1 - (W - 1 - x) / 2 ^ n

/-- The big-endian value of the first `n` bytes of the byte sequence `f` (`f 0` is the most significant). -/
def fromBE (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 * 256 ^ n + fromBE (fun i => f (i + 1)) n

/-- `z.ExtendSign(x, b)`: sign-extend `x` from byte `b` (byte 0 is the least significant). Unchanged when `b ≥ 31`. -/
def extendSign (x b : Nat) : Nat :=
  if b < 31 then
    (if x / 2 ^ (8 * b + 7) % 2 = 1 then x % 2 ^ (8 * b + 8) + (W - 2 ^ (8 * b + 8)) else x % 2 ^ (8 * b + 8))
  else x

/-- `z.SizeSSZ()`: the SSZ encoding of a `uint256` has 32 bytes. -/
def sizeSSZ : Nat := 32

end Fv256.Spec
