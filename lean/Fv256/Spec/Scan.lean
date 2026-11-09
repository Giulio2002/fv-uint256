import Fv256.Spec.I

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Fv256.I

namespace Fv256.ScanSpec

/-- the index of the first `'e'` among the first `n` bytes -/
def idxE (b : Nat → Nat) (n : Nat) : Option Nat := (List.range n).find? (fun i => b i == 101)

/-- the outcome of `scanScientificFromString` on the bytes `b 0 .. b (n-1)` -/
noncomputable def sciParse (b : Nat → Nat) (n : Nat) : Res :=
  if n = 0 then Res.ok 0 else
  match idxE b n with
  | none => decParse b n
  | some i =>
    match decParse b i with
    | Res.ok v =>
      if n - (i + 1) = 1 ∧ b (i + 1) = 48 then Res.ok v else
      match decParse (fun k => b (i + 1 + k)) (n - (i + 1)) with
      | Res.ok e => if 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e then Res.range else Res.ok (v * 10 ^ e)
      | Res.syntax lo len => Res.syntax (i + 1 + lo) len
      | r => r
    | r => r

end Fv256.ScanSpec
