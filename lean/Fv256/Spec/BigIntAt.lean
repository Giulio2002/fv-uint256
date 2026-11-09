import Fv256.Spec.IntoBigCommon

/-!
# Machine layout of a `math/big.Int` in memory, read as an integer

A Go `big.Int` is a 32-byte struct `{neg bool; abs []Word}`: sign byte at offset 0, limb pointer at 8, limb count at 16, limb capacity at 24.
`BigIntAt m P b` says: in memory `m` the object at `P` is a well-formed `big.Int` (sign flag clear, normalized, at most four limbs,
capacity at least four, readable/writable) whose integer value is `b`. (Only non-negative `b` arise from `uint256`, so the sign flag is clear.)
This is a machine-layout predicate; WHAT the value is comes from `Fv256/Spec/ToBig.lean`.
-/

namespace Fv256.Spec

/-- The object at `P` in memory `m` is a well-formed `big.Int` of integer value `b`. -/
def BigIntAt (m : Janus.Arm64.Memory) (P : Nat) (b : Int) : Prop :=
  ∃ v : Nat, b = (v : Int) ∧ Fv256.IntoBig.BigObj m P v

end Fv256.Spec
