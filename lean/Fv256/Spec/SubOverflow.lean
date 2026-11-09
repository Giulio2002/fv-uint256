/-!
# `func (z *Int) SubOverflow(x, y *Int) (*Int, bool)`

`z.SubOverflow(x, y)` sets `z = x - y` wrapped modulo `2^256` (exactly the value of `Sub`) and returns `z` together with a borrow flag. The flag is true exactly when `x < y` (the subtraction wrapped). It has no error or panic case.
-/

namespace Fv256.Spec

/-- Borrow flag of `z.SubOverflow(x, y)`: true exactly when `x < y`, i.e. the true difference is negative. (The stored value is `Fv256.Spec.sub x y`.) -/
def subOv (x y : Nat) : Bool := decide (x < y)

/-- Zero minus one borrows. -/
example : subOv 0 1 = true := by decide

/-- Equal numbers do not borrow. -/
example : subOv 7 7 = false := by decide

/-- A larger minuend does not borrow. -/
example : subOv 8 7 = false := by decide

end Fv256.Spec
