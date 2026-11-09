import Lean

/-!
# `close_eq_hyp`: close `a = b` by a local hypothesis `a = b'` with `b'` defeq `b` (state-projection equalities after calls)

Only hypotheses whose left-hand side is syntactically `a` are tried, so no unfolding of memory chains happens.
-/

open Lean Elab Tactic Meta

elab "close_eq_hyp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := ty.eq? | throwError "close_eq_hyp: goal is not an equation"
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      match dty.eq? with
      | some (_, l', _) =>
        if l' == lhs then
          if ← isDefEq dty ty then
            g.assign (mkFVar d.fvarId)
            replaceMainGoal []
            return
      | none => pure ()
    throwError "close_eq_hyp: no hypothesis with left-hand side {lhs}"
