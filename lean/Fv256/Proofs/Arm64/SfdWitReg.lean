import Fv256.Proofs.Arm64.SfdTopSpec

/-!
# Regression: the OLD `Mod` requirement was contradictory

Before the fix, `Mod` required every range of `staticRanges C T`, in particular `(T, T + 48)`, to lie outside `R2.priv`, while
`Env` contains `R2.IsType T` and a model environment, and `R2.Laws.type_desc` then puts `(T, T+48)` INSIDE `R2.priv`.
`mod_contra_old` proves the old requirement unsatisfiable (so `TopPre` held of no state); The positive statement that the new `TopPre` is
satisfied by a concrete call is `Fv256.Arm64.SetFromDecimal.Witness.pre0` (and, with the contracts, `nonvacuous`).
-/

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I

namespace Fv256.Arm64.SfdTopSpec

theorem mod_contra_old (C : SfdCfg) (R2 : IfaceModel) (T : Nat) (m : Janus.Arm64.Memory) (g : BitVec 64)
    (hl : R2.Laws) (hT : R2.IsType T) (hE : R2.Env m g)
    (hold : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) R2.priv) : False := by
  obtain ⟨-, -, -, hin⟩ := hl.type_desc m g T hE hT
  obtain ⟨r, hr, h1, h2⟩ := hin
  have ho : Outside T 48 R2.priv := by
    have := hold (T, T + 48) (by simp [staticRanges])
    simpa using this
  have := MemFrame.outside_mem ho hr
  have h3 : (48 : Nat) = typeDescSize := rfl
  omega

end Fv256.Arm64.SfdTopSpec
