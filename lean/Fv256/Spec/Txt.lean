import Fv256.Spec.PrettyMath

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.E

/-- `MarshalJSON`'s bytes of the number `v`: `"` digits `"`. -/
def marshalJSONBytes (v : Nat) : List Nat := 34 :: (decBytes v ++ [34])

end Fv256.E
