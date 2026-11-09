import Janus
import Fv256.Spec.Core

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.Util

/-- `m'` agrees with `m` and has the same regions outside two byte ranges `[p, p+n)` and `[q, q+k)`:
the result object and a callee's scratch (spill) slots below the stack pointer. -/
def OnlyWrites2 (m m' : Janus.Arm64.Memory) (p n q k : Nat) : Prop :=
  m'.regions = m.regions ∧ ∀ a, (a < p ∨ p + n ≤ a) → (a < q ∨ q + k ≤ a) → m'.bytes a = m.bytes a

section BEsec

open Janus.Arm64

end BEsec

section W16sec

open Janus.Arm64

end W16sec

section RC8

open Janus.Arm64

end RC8


-- byte `e/8` (from the low end) of a 256-bit number written as four limbs; stated with explicit literals so that it can be applied in omega-hostile contexts

section B20

open Janus.Arm64

end B20

-- MulOverflow helper

section WTS

open Janus.Arm64

end WTS

section CH32

open Janus.Arm64

end CH32

-- ByteLen amd64 helper

section SBQ

open Janus.Arm64

end SBQ

end Fv256.Util
