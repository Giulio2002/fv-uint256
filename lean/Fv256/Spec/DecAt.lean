import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.E

def DecAt (rt : List (Nat × Nat)) (t1 t2 t3 p l : Nat) : Prop :=
  Janus.InRanges p l rt ∨ (t1 ≤ p ∧ p + l ≤ t1 + 256) ∨ (t2 ≤ p ∧ p + l ≤ t2 + 256) ∨ (t3 ≤ p ∧ p + l ≤ t3 + 256)

end Fv256.E
