import Fv256.Proofs.Common.SpecC

/-!
# Documented specification of `FromBig` / `MustFromBig` / `SetFromBig`

Intended semantics (upstream issue #115, maintainer; written into the doc comments by PR #233; master
`conversion.go`): `FromBig(b)` "returns a new Int and whether overflow occurred". A negative `b` wraps to
`b mod 2^256` (two's complement); overflow occurs iff `|b| >= 2^256`. `MustFromBig` panics iff overflow occurred.

This file states that reading independently of the code, and proves that the machine-level quantities used in the
compiled-code theorems (`Fv256.C.fromBig` on the sign flag and the limb words, `Fv256.C.fromBigOv` on the word
count) are exactly the documented ones for a normalized `big.Int` (top word non-zero, which is the `nat` invariant).
-/

namespace Fv256.C

open Fv256.Spec

/-- documented overflow of `FromBig(b)`: `|b| >= 2^256`. -/
def fromBigDocOv (abs : Nat) : Bool := decide (2 ^ 256 ≤ abs)

/-- documented value of `FromBig(b)`: `b mod 2^256` (for the `big.Int` of sign flag `neg` and magnitude `abs`). -/
def fromBigDoc (neg : Bool) (abs : Nat) : Nat := (bigVal neg abs % (2 ^ 256 : Nat)).toNat

/-- the value computed by the code is the documented `b mod 2^256`, including for negative `b`. -/
theorem fromBig_eq_doc (neg : Bool) (abs : Nat) : fromBig neg abs = fromBigDoc neg abs := by
  unfold fromBig fromBigDoc bigVal Spec.neg Spec.W
  cases neg <;> simp <;> omega

theorem bigAbs_lt (w : Nat → Nat) (hw : ∀ i, w i < 2 ^ 64) : ∀ n, bigAbs w n < 2 ^ (64 * n)
  | 0 => by simp [bigAbs]
  | n + 1 => by
    have ih := bigAbs_lt w hw n
    have h1 := hw n
    have h2 : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    have h3 : w n * 2 ^ (64 * n) + 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) :=
      by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h1
    simp only [bigAbs]
    rw [h2]
    have := Nat.mul_comm (2 ^ 64) (2 ^ (64 * n))
    omega

theorem bigAbs_ge (w : Nat → Nat) (n : Nat) (hn : w n ≠ 0) : 2 ^ (64 * n) ≤ bigAbs w (n + 1) := by
  simp only [bigAbs]
  have : 1 * 2 ^ (64 * n) ≤ w n * 2 ^ (64 * n) := Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hn)
  omega

/-- for a normalized `big.Int` (words below `2^64`, top word non-zero) the code's overflow flag (more than 4
words) is exactly the documented `|b| >= 2^256`. -/
theorem fromBigOv_eq_doc (w : Nat → Nat) (hw : ∀ i, w i < 2 ^ 64) (len : Nat)
    (hnorm : len = 0 ∨ w (len - 1) ≠ 0) : fromBigOv len = fromBigDocOv (bigAbs w len) := by
  unfold fromBigOv fromBigDocOv
  by_cases h : 4 < len
  · have hne : w (len - 1) ≠ 0 := by
      rcases hnorm with h0 | h0
      · omega
      · exact h0
    have h1 := bigAbs_ge w (len - 1) hne
    have h2 : len - 1 + 1 = len := by omega
    rw [h2] at h1
    have h3 : 2 ^ 256 ≤ 2 ^ (64 * (len - 1)) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 256 ≤ 64 * (len - 1) by omega)
      exact this
    have h4 : 2 ^ 256 ≤ bigAbs w len := Nat.le_trans h3 h1
    simp [h, h4]
  · have h1 := bigAbs_lt w hw len
    have h3 : 2 ^ (64 * len) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
    have h4 : ¬ 2 ^ 256 ≤ bigAbs w len := by omega
    simp [h, h4]

end Fv256.C
