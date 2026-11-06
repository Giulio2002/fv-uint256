/-!
# Pure Nat lemmas for `uint256.Reciprocal` (Newton–Raphson refinement), Extracted-free

`newtonStep A Y r` is one exact Newton step for `A / Y` from the approximation `r`: `⌊(2·r·A − r²·Y) / A⌋`.
The defect `A − r·Y` squares at every step (`newton_defect`), and the iterate never overshoots (`newton_le`).
-/

namespace Fv256.RecipMath

def newtonStep (A Y r : Nat) : Nat := (2 * r * A - r * r * Y) / A

/-- the key identity: `Y (2 r A − r² Y) + (A − r Y)² = A²` (for `r Y ≤ A`) -/
theorem newton_id (A Y r : Nat) (h : r * Y ≤ A) :
    (2 * r * A - r * r * Y) * Y + (A - r * Y) * (A - r * Y) = A * A := by
  obtain ⟨e, he⟩ : ∃ e, A = r * Y + e := ⟨A - r * Y, by omega⟩
  have hN : 2 * r * A - r * r * Y = r * (r * Y) + 2 * r * e := by
    apply Nat.sub_eq_of_eq_add
    subst he; grind
  have h3 : A - r * Y = e := by omega
  rw [hN, h3, he]
  grind

/-- Newton from below never overshoots -/
theorem newton_le (A Y r : Nat) (hA : 0 < A) (h : r * Y ≤ A) : newtonStep A Y r * Y ≤ A := by
  unfold newtonStep
  have hid := newton_id A Y r h
  have h1 : (2 * r * A - r * r * Y) / A * A ≤ 2 * r * A - r * r * Y := Nat.div_mul_le_self _ _
  have h2 : (2 * r * A - r * r * Y) / A * Y * A ≤ (2 * r * A - r * r * Y) * Y := by
    have := Nat.mul_le_mul_right Y h1
    grind
  have h3 : (2 * r * A - r * r * Y) / A * Y * A ≤ A * A := by omega
  exact Nat.le_of_mul_le_mul_right h3 hA

/-- the defect after one Newton step: `A·(A − r'·Y) ≤ (A − r·Y)² + A·Y` -/
theorem newton_defect (A Y r : Nat) (hA : 0 < A) (h : r * Y ≤ A) :
    A * (A - newtonStep A Y r * Y) ≤ (A - r * Y) * (A - r * Y) + A * Y := by
  have hid := newton_id A Y r h
  have hle := newton_le A Y r hA h
  unfold newtonStep at *
  generalize hN : 2 * r * A - r * r * Y = N at *
  have hdm := Nat.div_add_mod N A
  have hlt := Nat.mod_lt N hA
  generalize N / A = q at *
  generalize N % A = rem at *
  have h5 : q * Y * A + rem * Y = N * Y := by
    have : (A * q + rem) * Y = N * Y := by rw [hdm]
    grind
  have h6 : rem * Y ≤ A * Y := Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have h7 : A * (A - q * Y) + q * Y * A = A * A := by
    have := Nat.sub_add_cancel hle
    have : A * (A - q * Y) + A * (q * Y) = A * A := by rw [← Nat.mul_add, this]
    grind
  omega

end Fv256.RecipMath
