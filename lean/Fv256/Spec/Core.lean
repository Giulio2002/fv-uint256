import Janus
import Fv256.Spec.Basic
import Fv256.Spec.Add   -- `Fv256.Spec.add` lives in its own pure file
import Fv256.Spec.AddOverflow
import Fv256.Spec.AddUint64
import Fv256.Spec.Sub
import Fv256.Spec.SubOverflow
import Fv256.Spec.SubUint64
import Fv256.Spec.Neg
import Fv256.Spec.Abs
import Fv256.Spec.Not
import Fv256.Spec.And
import Fv256.Spec.Or
import Fv256.Spec.Xor
import Fv256.Spec.Clear
import Fv256.Spec.Set
import Fv256.Spec.SetOne
import Fv256.Spec.SetAllOne
import Fv256.Spec.SetUint64
import Fv256.Spec.Lsh
import Fv256.Spec.Rsh
import Fv256.Spec.SRsh
import Fv256.Spec.ExtendSign
import Fv256.Spec.SizeSSZ   -- `Fv256.Spec.sizeSSZ` lives in its own pure file
import Fv256.Spec.Mul   -- `Fv256.Spec.mul` likewise

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.Spec

/-- `x.IsZero()`. -/
def isZero (x : Nat) : Bool := x == 0

/-- `z.Eq(x)`. -/
def eq (x y : Nat) : Bool := x == y

/-- `z.Lt(x)`: unsigned less-than. -/
def lt (x y : Nat) : Bool := decide (x < y)

/-- `z.Gt(x)`: unsigned greater-than. -/
def gt (x y : Nat) : Bool := decide (y < x)

/-- `z.Cmp(x)`: -1, 0 or 1. -/
def cmp (x y : Nat) : Int := if x < y then -1 else if x = y then 0 else 1


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

/-- `x.BitLen()`: the number of significant bits (`0` for zero, otherwise `⌊log₂ x⌋ + 1`). -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- `x.ByteLen()`: the number of bytes needed to hold the significant bits. -/
def byteLen (x : Nat) : Nat := (bitLen x + 7) / 8

/-- `z.Byte(n)` on the number `x`: the `n`-th byte of `x` counted from the most significant end
(`n = 0` is the top byte); `0` when `n ≥ 32`. -/
def byte (n x : Nat) : Nat := if n < 32 then x / 2 ^ (8 * (31 - n)) % 256 else 0


/-- `x.Uint64WithOverflow()` overflow flag: the number does not fit in 64 bits. -/
def uint64Ov (x : Nat) : Bool := decide (2 ^ 64 ≤ x)

/-- The big-endian value of the first `n` bytes of the byte sequence `f` (`f 0` is the most significant). -/
def fromBE (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 * 256 ^ n + fromBE (fun i => f (i + 1)) n


end Fv256.Spec
