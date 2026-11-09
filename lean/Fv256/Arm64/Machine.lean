import Extracted

/-!
# Machine-level vocabulary shared by the arm64 claims (`Fv256/Arm64/*.lean`)

The few predicates that more than one function's precondition needs. They state facts about WHERE things are in memory,
never about what a function computes (that is `Fv256/Spec/`). Everything else a precondition says comes straight from
`Janus.Arm64` / `Janus.GoABI` (`Ptr32`, `GuardOK`, `StackOK`, `Aliasing`, ...), documented in Janus.
-/

namespace Fv256.Arm64

/-- `p` and `q` each address a 32-byte `uint256.Int` and are either the same object or do not overlap at all (partial overlap
is excluded). -/
def Alias32 (p q : BitVec 64) : Prop := p = q ∨ p.toNat + 32 ≤ q.toNat ∨ q.toNat + 32 ≤ p.toNat

end Fv256.Arm64
