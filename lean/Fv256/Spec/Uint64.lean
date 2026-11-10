/-!
# `func (z *Int) Uint64() uint64`

`z.Uint64()` returns the low 64 bits of `z` (the value modulo `2^64`); higher bits are silently dropped. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Uint64()` (also the first result of `Uint64WithOverflow`): the number modulo `2^64`. -/
def uint64 (x : Nat) : Nat := x % 2 ^ 64

example : uint64 5 = 5 := by decide

/-- Truncation: `2^64 + 5` gives `5`. -/
example : uint64 (2 ^ 64 + 5) = 5 := by decide

end Fv256.Spec
