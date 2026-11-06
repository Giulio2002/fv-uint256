import Fv256.MulModMath
set_option maxHeartbeats 64000000
set_option exponentiation.threshold 1024
namespace Fv256.Arm64.R4Nat
open Fv256.F

theorem r_ok (x m q A Bl D C r8 : Nat) (hA : A = x % 2 ^ 320) (hBl : Bl = q * m % 2 ^ 320)
    (hlt : reduceR x m q < 2 ^ 320)
    (hr1 : r8 = 0 ↔ Bl ≤ A) (hr2 : r8 = 0 → D + Bl = A) (hr3 : r8 ≠ 0 → D + Bl = A + 2 ^ 320)
    (hf0 : r8 = 0 → C = D) (hf1 : r8 ≠ 0 → C = (D + m) % 2 ^ 320) : C = reduceR x m q := by
  have e : reduceR x m q = if A < Bl then (A + 2 ^ 320 - Bl) % 2 ^ 320 + m else (A + 2 ^ 320 - Bl) % 2 ^ 320 := by
    unfold reduceR
    simp only []
    rw [← hA, ← hBl]
  rw [e] at hlt ⊢
  by_cases h : r8 = 0
  · have h1 := hr1.1 h
    have h2 := hr2 h
    rw [if_neg (by omega), hf0 h]
    omega
  · have h1 : ¬ Bl ≤ A := fun hh => h (hr1.2 hh)
    have h2 := hr3 h
    rw [if_pos (by omega)] at hlt ⊢
    rw [hf1 h]
    omega

end Fv256.Arm64.R4Nat
