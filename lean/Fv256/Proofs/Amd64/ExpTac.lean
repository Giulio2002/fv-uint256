import Lean
-- omega_e: omega after dropping the pointer-disjointness disjunctions of Exp's context (they only cause exponential case splits).
set_option hygiene false in
macro "omega_e" : tactic =>
  `(tactic| (
      (try clear hdz)
      (try clear hdb)
      (try clear hde)
      (try clear hdg)
      omega))
