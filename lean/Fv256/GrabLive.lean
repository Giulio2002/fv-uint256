import Janus

/-!
# `fv_live_names`: content-based names for the results of a live allocation contract (`LiveAllocRet64`) after `janus64_run … calls [h]`

Names the inaccessible results of the LAST live call by their types, never by position:
`ptr : W64`, `junk kr : Nat → W64` (the last two), `f : Flags`, `x yh : Nat → BitVec 128` (the last two), `m : Memory`, `zh : Nat → BitVec 256`.
-/

namespace Fv256.GrabLive

open Lean Elab Tactic Meta

private def isFunBV (ty : Expr) (w : Nat) : Bool :=
  match ty with
  | .forallE _ d b _ => d.isConstOf ``Nat && !b.hasLooseBVars && b.isAppOfArity ``BitVec 1 && (b.getArg! 0).nat? == some w
  | _ => false

elab "fv_live_names " a0:ident a1:ident a2:ident a3:ident a4:ident a5:ident a6:ident a7:ident : tactic => do
  -- order of the names: ptr junk f x yh m zh kr
  let ids : Array Ident := #[a0, a1, a2, a3, a4, a5, a6, a7]
  let g ← getMainGoal
  let decl ← g.getDecl
  let mut lctx := decl.lctx
  let mut w64 : Array LocalDecl := #[]
  let mut fw64 : Array LocalDecl := #[]
  let mut bv128 : Array LocalDecl := #[]
  let mut zhD : Option LocalDecl := none
  let mut fD : Option LocalDecl := none
  let mut mD : Option LocalDecl := none
  for d in decl.lctx do
    if d.isImplementationDetail || !d.userName.hasMacroScopes then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if isFunBV ty 256 then zhD := some d
    else if isFunBV ty 128 then bv128 := bv128.push d
    else if ty.isForall && ty.bindingDomain!.isConstOf ``Nat then
      let b ← whnfR ty.bindingBody!
      if b.isAppOfArity ``BitVec 1 && (b.getArg! 0).nat? == some 64 then fw64 := fw64.push d
    else if ty.getAppFn.isConstOf ``Janus.Amd64.Flags then fD := some d
    else if ty.getAppFn.isConstOf ``Janus.Arm64.Memory then mD := some d
    else
      let b ← whnfR ty
      if b.isAppOfArity ``BitVec 1 && (b.getArg! 0).nat? == some 64 then w64 := w64.push d
  let some zh := zhD | throwError "fv_live_names: no Nat → BitVec 256 result"
  let some fd := fD | throwError "fv_live_names: no Flags result"
  let some md := mD | throwError "fv_live_names: no Memory result"
  unless w64.size ≥ 1 && fw64.size ≥ 2 && bv128.size ≥ 2 do throwError "fv_live_names: missing W64 / Nat → W64 / BitVec 128 results"
  let pairs : Array (LocalDecl × Name) := #[
    (w64[w64.size - 1]!, ids[0]!.getId), (fw64[fw64.size - 2]!, ids[1]!.getId), (fd, ids[2]!.getId),
    (bv128[bv128.size - 2]!, ids[3]!.getId), (bv128[bv128.size - 1]!, ids[4]!.getId), (md, ids[5]!.getId),
    (zh, ids[6]!.getId), (fw64[fw64.size - 1]!, ids[7]!.getId)]
  for (d, n) in pairs do
    lctx := lctx.setUserName d.fvarId n
  let g' ← mkFreshExprMVarAt lctx decl.localInstances decl.type
  g.assign g'
  replaceMainGoal [g'.mvarId!]

end Fv256.GrabLive
