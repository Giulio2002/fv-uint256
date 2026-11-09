/-!
# `func (z *Int) Clone() *Int`

`z.Clone()` allocates a fresh `Int` holding a copy of the number in `z` and returns a pointer to it. The new object is distinct from `z` and from everything the caller holds; `z` itself is not modified. No error or panic case (apart from running out of memory).
-/

namespace Fv256.Spec

/-- Number held by the object `z.Clone()` returns: the number `x` that `z` held, unchanged. -/
def clone (x : Nat) : Nat := x

/-- Clone copies the number. -/
example : clone 7 = 7 := by decide

end Fv256.Spec
