import Fv256.Spec.Format
import Fv256.Spec.FormatBytes
import Fv256.Proofs.Common.TextBridge

/-!
# Bridge for `Format`

The readable specification `Fv256.Spec.fastBytes` (digit lists built from Lean's `Nat.toDigits`, via `Spec.dec` and `Spec.hex`) agrees with the
implementation-shaped `Fv256.FormatSpec.fastBytes` the machine-level proofs of `Format` use.
-/

namespace Fv256.FormatBridge

/-- `FormatSpec.hexBytes` is the base-16 digit recursion `TextBridge.D 16` -/
theorem hexBytes_D (n : Nat) : Fv256.FormatSpec.hexBytes n = Fv256.TextBridge.D 16 n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Fv256.FormatSpec.hexBytes, Fv256.TextBridge.D_eq 16 n (by omega)]
    by_cases h : n < 16
    · simp [h, Fv256.TextBridge.dc]
    · have : n / 16 < n := Nat.div_lt_self (by omega) (by omega)
      simp [h, ih (n / 16) this, Fv256.TextBridge.dc]

/-- the hexadecimal digits of `Spec.hex` (after `0x`) are `FormatSpec.hexBytes` -/
theorem hex_drop2 (n : Nat) : (Fv256.Spec.hex n).drop 2 = Fv256.FormatSpec.hexBytes n := by
  unfold Fv256.Spec.hex
  simp only [List.drop_succ_cons, List.drop_zero]
  rw [Fv256.TextBridge.toDigits_eq 16 (by omega) (by omega), hexBytes_D]

/-- the machine-level `fastBytes` is the readable `Spec.fastBytes` (with the arguments in the other order) -/
theorem fastBytes_eq (z ch : Nat) : Fv256.FormatSpec.fastBytes z ch = Fv256.Spec.fastBytes ch z := by
  unfold Fv256.FormatSpec.fastBytes Fv256.Spec.fastBytes
  by_cases h : ch = 120
  · simp [h, hex_drop2]
  · simp [h, Fv256.TextBridge.dec_eq]

/-- the five bytes of `"<nil>"` -/
theorem nilText_eq : Fv256.FormatSpec.nilText = Fv256.Spec.nilText := rfl

end Fv256.FormatBridge
