import Janus
open Lean Elab Tactic Meta

/-- clear every hypothesis that mentions an explicit machine-state literal (the callee summary's register/`pc` equalities after a
call): they are only needed by the executor, and make `simp at *`/`generalize at *` very slow -/
elab "clear_states" : tactic => do
  let g ← getMainGoal
  let mut g := g
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isAppOf ``Janus.Arm64.State.mk).isSome then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

example (s : Janus.Arm64.State) (h : s = { s with pc := 5 }) (h2 : 1 = 1) : True := by
  clear_states
  trace_state
  trivial
