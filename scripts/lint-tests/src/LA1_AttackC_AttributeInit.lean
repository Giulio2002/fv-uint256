import SvyTools
import Lean
open Lean

namespace Fv256.AttackC
/-- RT13 LA3: `attribute [init]` form (not `@[init]`), no `initialize` keyword. -/
def hookv : IO Nat := pure 3
opaque cell : Nat
attribute [init hookv] cell
end Fv256.AttackC
