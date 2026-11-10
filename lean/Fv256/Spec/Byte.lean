/-!
# `func (z *Int) Byte(n *Int) *Int`

`z.Byte(n)` replaces `z` by the `n`-th byte of `z` counted from the MOST significant end (`n = 0` is the top byte, `n = 31`
the lowest), as a number in `0..255`. If `n >= 32` (any value of the 256-bit `n`) the result is `0`. It returns `z`. No panic.
-/

namespace Fv256.Spec

/-- Value of `z.Byte(n)` where `x` is the number held by `z` before the call: the byte of `x` at big-endian index `n`, or `0`
when `n >= 32`. (Argument order: the index `n` first, the number `x` second.) -/
def byte (n x : Nat) : Nat := if n < 32 then x / 2 ^ (8 * (31 - n)) % 256 else 0

/-- Index 0 is the most significant byte. -/
example : byte 0 (7 * 2 ^ 248) = 7 := by decide

/-- Index 31 is the least significant byte. -/
example : byte 31 0x1234 = 0x34 := by decide

/-- Out of range gives zero (also for a huge index). -/
example : byte 32 0x1234 = 0 := by decide
example : byte (2 ^ 200) 0x1234 = 0 := by decide

end Fv256.Spec
