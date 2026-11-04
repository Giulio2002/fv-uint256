import Lean

/-!
Debug helper for proof development (not used by any verified theorem): `print_goal_first` throws an error whose first line is
the main goal, so tools that truncate long error messages (the `janus verify` output) still show the goal before the long hypothesis list.
-/
open Lean Elab Tactic in
elab "print_goal_first" : tactic => do
  let g ← getMainTarget
  throwError m!"GOAL: {g}"

open Lean Meta Elab Tactic in
/-- `print_ctx_first`: like `print_goal_first` but also lists the hypotheses (props only), skipping simple `x < 2 ^ 64` / `x < 18446744073709551616` bounds, goal first. -/
elab "print_ctx_first" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut out : String := s!"GOAL: {← ppExpr (← g.getType)}\n"
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      unless (← isProp d.type) do continue
      let t := toString (← ppExpr d.type)
      if (t.splitOn "< 18446744073709551616").length > 1 && t.length < 90 then continue
      if (t.splitOn "< 2 ^ 64").length > 1 && t.length < 60 then continue
      out := out ++ s!"{d.userName}: {t.replace "\n" " "}\n"
    throwError out

open Lean Elab Tactic in
/-- `log_goal "tag"`: logs the main goal as an error (so it shows up in truncated verify output) and CONTINUES, so several stages of one proof can be inspected in a single run. The proof still fails. -/
elab "log_goal " tag:str : tactic => do
  let g ← getMainTarget
  logError m!"{tag.getString}: {g}"

open Lean Meta Elab Tactic in
/-- `goal_summary`: logs, for each open goal, its index and the head symbol / first 200 chars of its target, then continues. -/
elab "goal_summary" : tactic => do
  let gs ← getGoals
  let mut i : Nat := 0
  for g in gs do
    let t ← g.getType
    let s ← (try pure (toString (← ppExpr t)) catch _ => pure "<unprintable>")
    logInfo m!"goal {i}/{gs.length}: {s.take 300}"
    i := i + 1

open Lean Meta Elab Tactic in
/-- `print_chains`: for every `Memory.readLE m a n` in the goal, prints `a`, `n` (raw `dbgToString`, robust to loose bvars) and the (addr, size) of each write in `m`, values omitted. -/
elab "print_chains" : tactic => do
  let g ← getMainTarget
  let acc ← IO.mkRef (#[] : Array String)
  let rec go (e : Expr) : MetaM Unit := do
    if e.getAppFn.constName?.any (fun n => n.toString.endsWith "Memory.readLE") && e.getAppNumArgs == 3 then
      let args := e.getAppArgs
      let mut m := args[0]!
      let mut ws : Array String := #[]
      while m.getAppFn.constName?.any (fun n => n.toString.endsWith "Memory.writeLE") && m.getAppNumArgs == 4 do
        let a := m.getAppArgs
        ws := ws.push s!"({a[1]!.dbgToString} , {a[2]!.dbgToString})"
        m := a[0]!
      acc.modify (·.push s!"READ {args[1]!.dbgToString} {args[2]!.dbgToString} <- {ws}")
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ => go t; go b
    | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go g
  let r ← acc.get
  throwError m!"CHAINS:\n{"\n".intercalate r.toList}"
