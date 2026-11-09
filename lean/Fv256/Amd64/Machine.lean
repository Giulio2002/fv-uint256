import Extracted

/-!
# Machine-level vocabulary shared by the amd64 claims (`Fv256/Amd64/*.lean`)

The few predicates that more than one function's precondition needs. They state facts about WHERE things are in memory,
never about what a function computes (that is `Fv256/Spec/`). Everything else a precondition says comes straight from
`Janus.Amd64.GoABI` (`Buffer`, `StackWritable`, `StackGuardOK`, ...), documented in Janus.
-/

open Janus.Amd64 Janus.Amd64.GoABI

namespace Fv256.Amd64

/-- `p` and `q` each address a 32-byte `uint256.Int` and are either the same object or do not overlap at all (partial overlap is
excluded). This is how `z.Add(z, x)`, `z.Add(x, x)` ... are allowed while torn aliasing is not. -/
def Alias32 (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32

/-- The `n` bytes at `p` lie entirely outside the byte range `[lo, hi)` (used for "the argument does not overlap the callee's
stack frame"). -/
def Outside (p : BitVec 64) (n lo hi : Nat) : Prop := p.toNat + n ≤ lo ∨ hi ≤ p.toNat

end Fv256.Amd64
