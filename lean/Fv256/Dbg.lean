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
