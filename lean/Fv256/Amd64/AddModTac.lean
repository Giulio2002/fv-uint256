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

/-- pure pre-order collection of the `p` of every `(decide p).toNat` (no mutable cells: Fv256 tactics may not use IO/ST refs) -/
partial def collectDecideToNat (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e, a)
  if e.isAppOfArity ``Bool.toNat 1 && e.appArg!.isAppOfArity ``Decidable.decide 2 then
    let p := e.appArg!.appFn!.appArg!
    modify fun (v, a) => (v, if a.contains p then a else a.push p)
  match e with
  | .app f a => collectDecideToNat f; collectDecideToNat a
  | .lam _ t b _ => collectDecideToNat t; collectDecideToNat b
  | .forallE _ t b _ => collectDecideToNat t; collectDecideToNat b
  | .letE _ t v b _ => collectDecideToNat t; collectDecideToNat v; collectDecideToNat b
  | .mdata _ b => collectDecideToNat b
  | .proj _ _ b => collectDecideToNat b
  | _ => pure ()

/-- add `(decide p).toNat ≤ 1 ∧ ((decide p).toNat = 1 ↔ p)` for each `(decide p).toNat` occurring in the listed hyps/goal -/
elab "decide_facts" : tactic => do
  let g ← getMainGoal
  let exprs ← g.withContext do
    let mut es : Array Expr := #[← g.getType]
    for d in (← getLCtx) do
      unless d.isImplementationDetail do es := es.push d.type
    return es
  let (_, found) := (exprs.forM collectDecideToNat).run ({}, #[]) |>.2
  for p in found do
    evalTactic (← `(tactic| have := Fv256_dtn2 $(← Term.exprToSyntax p)))

end
