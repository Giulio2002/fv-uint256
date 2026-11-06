import Lean
import Janus

/-!
# Content-based lookup of facts (the single shared implementation: `grab_const`, `grab_frame`, `grab_proj_of`)

Type-based lookup of facts after `janus64_run … calls [..]` / `janus_run … calls [..]`

Positional `rename_i` re-binds names silently when a callee summary gains or reorders conjuncts.  `grab_const c as h` names `h`
the first local hypothesis whose type mentions the constant `c`, whatever its position.
-/

open Lean Elab Tactic Meta

namespace Fv256.GrabTac

/-- does `e` contain the numeral `n` (as `OfNat.ofNat _ n _` or a raw literal)? -/
def hasNumeral (e : Expr) (n : Nat) : Bool :=
  (e.find? fun x =>
    (x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 1).rawNatLit? == some n) || x.rawNatLit? == some n).isSome

end Fv256.GrabTac

/-- `grab_const c as h`: name `h` the first local hypothesis whose type mentions the constant `c`. -/
elab "grab_const " c:ident " as " n:ident : tactic => do
  let cn ← realizeGlobalConstNoOverloadWithInfo c
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isConstOf cn).isSome then
      let (_, g') ← g.withContext (g.note n.getId (mkFVar d.fvarId) ty)
      replaceMainGoal [g']
      return
  throwError "grab_const: no hypothesis mentions {cn}"

/-- `grab_frame k as h`: name `h` the first `MemFrame` hypothesis whose range list mentions the numeral `k`
(the callee's output object is at `SP - k`). -/
elab "grab_frame " k:num " as " n:ident : tactic => do
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Janus.MemFrame && Fv256.GrabTac.hasNumeral ty.getAppArgs.back! k.getNat then
      let (_, g') ← g.withContext (g.note n.getId (mkFVar d.fvarId) ty)
      replaceMainGoal [g']
      return
  throwError "grab_frame: no MemFrame hypothesis mentions {k.getNat}"

/-- `grab_proj_of fr f i as h`: name `h` the hypothesis `st.f i = _` where `st` is the returned state of the callee whose
`MemFrame` hypothesis is `fr` (its final memory is `st.mem`); selected by content, not by position. -/
elab "grab_proj_of " fr:ident f:ident i:num " as " n:ident : tactic => do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let some fd := lctx.findFromUserName? fr.getId | throwError "grab_proj_of: no hypothesis {fr.getId}"
  let fty ← instantiateMVars fd.type
  let m' := fty.getAppArgs[fty.getAppArgs.size - 2]!
  let stFv ← match m'.getAppArgs.back? with
    | some (.fvar id) => pure id
    | _ => throwError "grab_proj_of: frame memory is not `st.mem` for a local state"
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    match ty.eq? with
    | some (_, lhs, _) =>
      let fn := lhs.getAppFn
      let args := lhs.getAppArgs
      if args.size ≥ 2 && fn.constName?.map (·.getString!) == some f.getId.toString then
        let okSt := match args[args.size - 2]! with
          | .fvar id => id == stFv
          | _ => false
        let idxArg := args[args.size - 1]!
        let okIdx := (idxArg.isAppOfArity ``OfNat.ofNat 3 && (idxArg.getArg! 1).rawNatLit? == some i.getNat) ||
          idxArg.rawNatLit? == some i.getNat
        if okSt && okIdx then
          let (_, g') ← g.withContext (g.note n.getId (mkFVar d.fvarId) ty)
          replaceMainGoal [g']
          return
    | none => pure ()
  throwError "grab_proj_of: no hypothesis st.{f.getId} {i.getNat} = _ for the state of {fr.getId}"
