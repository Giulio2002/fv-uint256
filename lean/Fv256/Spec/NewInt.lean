/-!
# `func NewInt(val uint64) *Int`

`uint256.NewInt(val)` allocates a fresh `Int` holding the 64-bit unsigned number `val` (upper 192 bits zero) and returns a pointer to it. The allocation is a new object, so it aliases nothing the caller holds. No error or panic case (apart from running out of memory, which the runtime reports itself).
-/

namespace Fv256.Spec

/-- Number held by the object `uint256.NewInt(val)` returns: `val` itself. -/
def newInt (val : Nat) : Nat := val

/-- NewInt stores the number as is. -/
example : newInt 7 = 7 := by decide

end Fv256.Spec
