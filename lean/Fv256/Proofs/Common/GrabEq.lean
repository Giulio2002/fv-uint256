import Lean
import Fv256.Proofs.Common.GrabTac

/-!
# `grab_eq st f [i] as h`: name the hypothesis `st.f [i] = _` (state field equation) by content

Like `Fv256.GrabTac`'s `grab_const`, never positional: after `janus_run … calls [dec_summary_ext …]` the callee's frame
equations (`s'.regs 4 = _`, `s'.sp = _`, `s'.pc = _`, `s'.xmm 15 = _`) are found by the state and the field.
-/
open Lean Elab Tactic Meta

namespace Fv256.GrabEq

private def isNum (e : Expr) (n : Nat) : Bool :=
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some n) || e.rawNatLit? == some n

private def grabCore (st f : Ident) (idx : Option Nat) (n : Ident) : TacticM Unit := do
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    if lhs.getAppFn.constName?.map (·.getString!) != some f.getId.toString then continue
    let args := lhs.getAppArgs
    let okSt (e : Expr) : MetaM Bool := do
      match e with
      | .fvar id => return ((← g.getDecl).lctx.find? id).any (·.userName == st.getId)
      | _ => return false
    match idx with
    | some i =>
      if args.size ≥ 2 && (← okSt args[args.size - 2]!) && isNum args.back! i then
        let (_, g') ← g.withContext (g.note n.getId (mkFVar d.fvarId) ty)
        replaceMainGoal [g']; return
    | none =>
      if args.size ≥ 1 && (← okSt args.back!) then
        let (_, g') ← g.withContext (g.note n.getId (mkFVar d.fvarId) ty)
        replaceMainGoal [g']; return
  throwError "grab_eq: no hypothesis {st.getId}.{f.getId}{idx.map (fun i => s!" {i}") |>.getD ""} = _"

elab "grab_eq " st:ident f:ident i:num " as " n:ident : tactic => grabCore st f (some i.getNat) n
elab "grab_eq " st:ident f:ident " as " n:ident : tactic => grabCore st f none n

/-- `grab_frame_last k as h`: the LAST hypothesis that IS a `MemFrame …` (not an implication into one) whose range list
mentions the numeral `k` (the callee's output frame; a later `v < 100 → MemFrame …` conjunct is a forall and never matches). -/
elab "grab_frame_last " k:num " as " n:ident : tactic => do
  let g ← getMainGoal
  let mut found : Option (FVarId × Expr) := none
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf `Janus.MemFrame && Fv256.GrabTac.hasNumeral ty.getAppArgs.back! k.getNat then found := some (d.fvarId, ty)
  match found with
  | some (fv, ty) =>
    let (_, g') ← g.withContext (g.note n.getId (mkFVar fv) ty)
    replaceMainGoal [g']
  | none => throwError "grab_frame_last: no MemFrame hypothesis mentions {k.getNat}"

/-- `clear_frame_imps`: clear every hypothesis of the form `P → MemFrame …` (a conditional frame fact the proof does not use,
e.g. dec_summary_ext's `v < 100 → MemFrame …` conjunct). Left in context, omega case-splits on its premise at every call. -/
elab "clear_frame_imps" : tactic => do
  let g ← getMainGoal
  let mut ids : Array FVarId := #[]
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall && !ty.bindingBody!.hasLooseBVars && ty.bindingBody!.isAppOf `Janus.MemFrame then ids := ids.push d.fvarId
  let mut g := g
  for i in ids.reverse do
    g ← g.tryClear i
  replaceMainGoal [g]

end Fv256.GrabEq
