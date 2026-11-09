/-!
# `func (z *Int) IAdd(x *Int) *Int`

`z.IAdd(x)` adds `x` to `z` in place: `z = z + x` with wrap-around (modulo `2^256`), and returns `z`. It is `z.Add(z, x)`. No error or panic case.
-/

namespace Fv256.Spec

/-- New value of `z` after `z.IAdd(x)`, where `z` is its value before the call: the sum wrapped modulo `2^256`. -/
def iAdd (z x : Nat) : Nat := (z + x) % 2 ^ 256

/-- Wrap-around. -/
example : iAdd (2 ^ 256 - 1) 1 = 0 := by decide

/-- Small numbers add as usual. -/
example : iAdd 2 3 = 5 := by decide

end Fv256.Spec
