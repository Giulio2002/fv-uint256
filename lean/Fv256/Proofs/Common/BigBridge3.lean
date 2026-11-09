import Fv256.Spec.BigIntAt
import Fv256.Spec.ToBig
import Fv256.Spec.IntoBig

/-!
# Bridge: `BigIntAt` / `BigIntSlot` (readable integer value) versus the proofs' `BigObj` / `BigOut` (natural-number value)
-/

namespace Fv256.Proofs.Big

open Fv256.Spec

theorem bigIntAt_iff (m : Janus.Arm64.Memory) (P v : Nat) : BigIntAt m P (toBig v) ↔ Fv256.IntoBig.BigObj m P v := by
  unfold BigIntAt toBig
  constructor
  · rintro ⟨w, hw, h⟩
    have : w = v := by omega
    subst this; exact h
  · intro h; exact ⟨v, rfl, h⟩

theorem bigIntSlot_iff (m : Janus.Arm64.Memory) (bp P v : Nat) : BigIntSlot m bp P (intoBig v) ↔ Fv256.IntoBig.BigOut m bp P v := by
  unfold BigIntSlot intoBig
  constructor
  · rintro ⟨w, hw, h⟩
    have : w = v := by omega
    subst this; exact h
  · intro h; exact ⟨v, rfl, h⟩

end Fv256.Proofs.Big
