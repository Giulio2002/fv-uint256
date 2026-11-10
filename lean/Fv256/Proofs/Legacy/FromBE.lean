/-!
# `Spec.fromBE`: the implementation-shaped big-endian reader used by the released proofs

`fromBE f n` is the big-endian value of the first `n` bytes `f 0, ..., f (n-1)` (`f 0` most significant). The readable specification
`Fv256.Spec.setBytes` (`Spec/SetBytes.lean`) is shown equal to it by `Proofs/Common/SetBytesBridge.lean`; the tactic proofs of the `SetBytesN`
rows still unfold this form, so it lives with the proofs and is not part of any statement.
-/

namespace Fv256.Spec

/-- The big-endian value of the first `n` bytes of the byte sequence `f` (`f 0` is the most significant). -/
def fromBE (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 * 256 ^ n + fromBE (fun i => f (i + 1)) n

end Fv256.Spec
