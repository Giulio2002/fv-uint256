import Fv256.Spec.SetBytes
import Fv256.Proofs.Common.Spec

/-!
# Bridge: the readable `Spec.setBytes` / `Spec.setBytesN` and the implementation-shaped `Spec.fromBE`

The compiled-code proofs (`Fv256/Proofs/{Amd64,Arm64}/SetBytes*.lean`) were written against `Spec.fromBE` with the used bytes addressed as
`ptr + len - used + i`. The readable claims (`Fv256/{Amd64,Arm64}/SetBytes*.lean`) state the result with `Spec.setBytes`. This file proves
the two agree, so the claims are equivalent to the originally released statements.
-/

namespace Fv256.Proofs.SetBytes

/-- `Spec.bigEndian` and `Spec.fromBE` are the same function. -/
theorem bigEndian_eq_fromBE : ∀ (n : Nat) (f : Nat → Nat), Fv256.Spec.bigEndian f n = Fv256.Spec.fromBE f n
  | 0, _ => rfl
  | n + 1, f => by simp [Fv256.Spec.bigEndian, Fv256.Spec.fromBE, bigEndian_eq_fromBE n]

/-- `Spec.setBytes` of a buffer starting at address `ptr` (byte `i` is `rd (ptr + i)`) is `fromBE` of the last `usedLen len` bytes,
addressed from `ptr + len - usedLen len`. -/
theorem setBytes_eq_fromBE (rd : Nat → Nat) (ptr len : Nat) :
    Fv256.Spec.setBytes (fun i => rd (ptr + i)) len =
      Fv256.Spec.fromBE (fun i => rd (ptr + len - Fv256.Spec.usedLen len + i)) (Fv256.Spec.usedLen len) := by
  have hu : Fv256.Spec.usedLen len ≤ len := by unfold Fv256.Spec.usedLen; split <;> omega
  unfold Fv256.Spec.setBytes
  rw [bigEndian_eq_fromBE]
  have : ∀ i, ptr + (len - Fv256.Spec.usedLen len + i) = ptr + len - Fv256.Spec.usedLen len + i := by intro i; omega
  simp only [this]

end Fv256.Proofs.SetBytes
