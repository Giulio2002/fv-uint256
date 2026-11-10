import Janus
import Fv256.Spec.C
import Fv256.Spec.BigInt
import Fv256.Spec.SetFromBig
import Fv256.Spec.CmpBig
import Fv256.Spec.FromBig
import Fv256.Spec.MustFromBig

/-!
# Bridge: the readable `big.Int` specifications (`Spec/BigInt.lean`, `SetFromBig`, `CmpBig`, `FromBig`, `MustFromBig`) versus
the implementation-shaped ones the proofs of the big-integer functions use (`Fv256.C.bigAbs`, `fromBig`, `bigVal`, `cmpBig`, `fromBigOv`)

The readable spec says `z = b mod 2^256` for the integer `b`; the proofs were written against "reduce the magnitude modulo `2^256`, negate
modulo `2^256` when the sign flag is set". The lemmas below prove those the same thing, once, for every sign, limb function and limb count.
-/

namespace Fv256.Proofs.Big

open Fv256.Spec

theorem bigMagnitude_eq (limb : Nat → Nat) (n : Nat) : bigMagnitude limb n = Fv256.C.bigAbs limb n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bigMagnitude, Fv256.C.bigAbs, ih]

/-- The readable `b mod 2^256` is the implementation-shaped "magnitude mod `2^256`, negated modulo `2^256` when the sign flag is set". -/
theorem setFromBig_bigValue (neg : Bool) (limb : Nat → Nat) (n : Nat) :
    setFromBig (bigValue neg limb n) = Fv256.C.fromBig neg (Fv256.C.bigAbs limb n) := by
  rw [← bigMagnitude_eq]
  unfold setFromBig bigValue Fv256.C.fromBig Fv256.Spec.neg Fv256.Spec.W
  cases neg <;> simp <;> omega

theorem bigVal_bigValue (neg : Bool) (limb : Nat → Nat) (n : Nat) :
    bigValue neg limb n = Fv256.C.bigVal neg (Fv256.C.bigAbs limb n) := by
  rw [← bigMagnitude_eq]; rfl

theorem cmpBig_bigValue (z : Nat) (neg : Bool) (limb : Nat → Nat) (n : Nat) :
    cmpBig z (bigValue neg limb n) = Fv256.C.cmpBig z (Fv256.C.bigVal neg (Fv256.C.bigAbs limb n)) := by
  rw [bigVal_bigValue]; rfl

theorem overflow_eq (n : Nat) : setFromBigOverflow n = Fv256.C.fromBigOv n := rfl

end Fv256.Proofs.Big
