import Lean
-- omega_s: omega after dropping the pointer-disjointness disjunctions (they only cause exponential case splits).
set_option hygiene false in
macro "omega_s" : tactic =>
  `(tactic| (
      (try clear hdx)
      (try clear hdy)
      (try clear hdm)
      (try clear hxd)
      (try clear hyd)
      (try clear hmd)
      (try clear hzm)
      (try clear hzx)
      (try clear hzy)
      (try clear hdg)
      (try clear hdgz)
      omega))

section
open Lean Elab Tactic Meta

theorem Fv256_dtn2 (p : Prop) [Decidable p] : (decide p).toNat ≤ 1 ∧ ((decide p).toNat = 1 ↔ p) := by
  by_cases p <;> simp [*]

/-- add `(decide p).toNat ≤ 1 ∧ ((decide p).toNat = 1 ↔ p)` for each `(decide p).toNat` occurring in the listed hyps/goal -/
elab "decide_facts" : tactic => do
  let g ← getMainGoal
  let exprs ← g.withContext do
    let mut es : Array Expr := #[← g.getType]
    for d in (← getLCtx) do
      unless d.isImplementationDetail do es := es.push d.type
    return es
  let ref ← IO.mkRef (#[] : Array Expr)
  for e in exprs do
    e.forEachWhere (fun e => e.isAppOfArity ``Bool.toNat 1) fun e => do
      match e.appArg!.isAppOfArity ``Decidable.decide 2 with
      | true => let p := e.appArg!.appFn!.appArg!
                ref.modify fun ps => if ps.contains p then ps else ps.push p
      | false => pure ()
  for p in (← ref.get) do
    evalTactic (← `(tactic| have := Fv256_dtn2 $(← Term.exprToSyntax p)))

end
