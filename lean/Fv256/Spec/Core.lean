import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


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

/-- `x.Uint64()`: the low 64 bits. -/
def uint64 (x : Nat) : Nat := x % 2 ^ 64

/-- `x.IsUint64()`: the number fits in 64 bits. -/
def isUint64 (x : Nat) : Bool := decide (x < 2 ^ 64)

/-- `x.Sign()`: the sign of the two's-complement reading: 0, 1 (positive) or -1 (negative, top bit set). -/
def sign (x : Nat) : Int := if x = 0 then 0 else if x < 2 ^ 255 then 1 else -1

/-- The two's-complement reading of a 256-bit number. -/
def signed (x : Nat) : Int := if x < 2 ^ 255 then (x : Int) else (x : Int) - 2 ^ 256

/-- `z.Slt(x)`: signed less-than. -/
def slt (x y : Nat) : Bool := decide (signed x < signed y)

/-- `z.Sgt(x)`: signed greater-than. -/
def sgt (x y : Nat) : Bool := decide (signed y < signed x)

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

/-- `x.BitLen()`: the number of significant bits (`0` for zero, otherwise `⌊log₂ x⌋ + 1`). -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- `x.ByteLen()`: the number of bytes needed to hold the significant bits. -/
def byteLen (x : Nat) : Nat := (bitLen x + 7) / 8

/-- `z.Byte(n)` on the number `x`: the `n`-th byte of `x` counted from the most significant end
(`n = 0` is the top byte); `0` when `n ≥ 32`. -/
def byte (n x : Nat) : Nat := if n < 32 then x / 2 ^ (8 * (31 - n)) % 256 else 0

/-- `z.Abs(x)`: the absolute value of the two's-complement reading, modulo `2^256`. -/
def abs (x : Nat) : Nat := if x < 2 ^ 255 then x else (W - x) % W

/-- `z.Lsh(x, n)`: shift left by `n` bits, modulo `2^256` (zero once `n ≥ 256`). -/
def lsh (x n : Nat) : Nat := (x * 2 ^ n) % W

/-- `z.Rsh(x, n)`: logical shift right by `n` bits (zero once `n ≥ 256`). -/
def rsh (x n : Nat) : Nat := x / 2 ^ n

/-- `z.SRsh(x, n)`: arithmetic shift right of the two's-complement reading of `x` by `n` bits (floor division), as `~(~x >> n)` for negative `x`. -/
def srsh (x n : Nat) : Nat := if x < W / 2 then x / 2 ^ n else W - 1 - (W - 1 - x) / 2 ^ n

/-- `x.Uint64WithOverflow()` overflow flag: the number does not fit in 64 bits. -/
def uint64Ov (x : Nat) : Bool := decide (2 ^ 64 ≤ x)

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
