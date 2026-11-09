import Janus

/-!
`fv_carry_simp_v1`: `janus_carry_simp` exactly as at Janus 655a23fa (amd64 vocabulary and the discharger without the
`janus_bounds_only; omega` alternative).  The generated amd64 `Reciprocal` segments were produced with it; at 5b023ef3 /
77fb30cc the extra discharger alternative makes borrow terms rewrite on one side of a goal only (see NOTES-B7).
-/

namespace Janus.Tactic

macro "fv_carry_disch_v1" : tactic =>
  `(tactic| first
    | assumption
    | exact Nat.sub_le _ _
    | exact Bool.toNat_le _
    | exact Nat.mod_lt _ (by decide)
    | exact Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt _ _ _) (by decide)
    | exact Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)
    | exact Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.le_refl _))

macro "fv_carry_simp_v1" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := fv_carry_disch_v1) only [Janus.Amd64.subFlags_fst_toNat_ofNat, Janus.Amd64.borrow64_toNat, Janus.Amd64.borrow64_in_toNat, Nat.reducePow] $[$loc]?)

end Janus.Tactic
