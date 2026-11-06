import Janus

/-!
# Where `Dec`'s result string lives

`DecAt rt t1 t2 t3 p l`: the string `(p, l)` returned by `Dec` / `FormatUint` is inside the runtime-owned ranges `rt` (a
`slicebytetostring` allocation), or inside one of the three read-only tables `t1, t2, t3` of 256 bytes (the digits,
the two-digit pairs and the zero string: the code returns a pointer into them for short results).
-/

namespace Fv256.E

def DecAt (rt : List (Nat × Nat)) (t1 t2 t3 p l : Nat) : Prop :=
  Janus.InRanges p l rt ∨ (t1 ≤ p ∧ p + l ≤ t1 + 256) ∨ (t2 ≤ p ∧ p + l ≤ t2 + 256) ∨ (t3 ≤ p ∧ p + l ≤ t3 + 256)

end Fv256.E
