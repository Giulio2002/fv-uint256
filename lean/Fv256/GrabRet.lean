import Janus

/-!
# `fv_ret_names`: content-based names for the results of an `ICallContract64` after `janus64_run … calls [h]`

Names the inaccessible results of the LAST icall by what they are (their types), never by position:
`junk kr : Nat → W64` (the last two), `x yh : Nat → BitVec 128` (the last two), `zh : Nat → BitVec 256`,
`f : Flags`, `m : Memory`, `hpr` (mentions `RtPreserves64`), `hfr` (the last `MemFrame`), `hR` (the last other proposition
that is not the `keep` hypothesis).  Replaces a positional `rename_i junk f x yh m zh kr hkeep hpr hfr hR`.
-/

namespace Fv256.GrabRet

open Lean Elab Tactic Meta

private def isFun (ty : Expr) (dom cod : Name) : Bool :=
  match ty with
  | .forallE _ d b _ => d.isConstOf dom && !b.hasLooseBVars && b.getAppFn.isConstOf cod
  | _ => false

private def isFunBV (ty : Expr) (w : Nat) : Bool :=
  match ty with
  | .forallE _ d b _ => d.isConstOf ``Nat && !b.hasLooseBVars && b.isAppOfArity ``BitVec 1 &&
      (b.getArg! 0).nat? == some w
  | _ => false

elab "fv_ret_names " a0:ident a1:ident a2:ident a3:ident a4:ident a5:ident a6:ident a7:ident a8:ident a9:ident : tactic => do
  let ids : Array Ident := #[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  -- expected order of the names: junk f x yh m zh kr hpr hfr hR
  let g ← getMainGoal
  let decl ← g.getDecl
  let mut lctx := decl.lctx
  let mut w64 : Array LocalDecl := #[]
  let mut bv128 : Array LocalDecl := #[]
  let mut zhD : Option LocalDecl := none
  let mut fD : Option LocalDecl := none
  let mut mD : Option LocalDecl := none
  let mut prD : Option LocalDecl := none
  let mut frD : Option LocalDecl := none
  let mut rD : Option LocalDecl := none
  for d in decl.lctx do
    if d.isImplementationDetail || !d.userName.hasMacroScopes then continue
    let ty ← instantiateMVars d.type
    if isFunBV ty 256 then zhD := some d
    else if isFunBV ty 128 then bv128 := bv128.push d
    else if ty.isForall && ty.bindingDomain!.isConstOf ``Nat && (ty.bindingBody!.getAppFn.isConstOf ``BitVec || ty.bindingBody!.getAppFn.isConst) then
      -- Nat → W64 (an abbreviation for BitVec 64) : recognised through whnfR
      let b ← whnfR ty.bindingBody!
      if b.isAppOfArity ``BitVec 1 && (b.getArg! 0).nat? == some 64 then w64 := w64.push d
    else if ty.isConstOf ``Janus.Amd64.Flags || ty.getAppFn.isConstOf ``Janus.Amd64.Flags then fD := some d
    else if ty.getAppFn.isConstOf ``Janus.Arm64.Memory then mD := some d
    else if (ty.find? fun e => e.isConstOf `Janus.Contracts.ICall.RtPreserves64).isSome then prD := some d
    else if ty.isAppOf `Janus.MemFrame then frD := some d
    else if (← isProp ty) && !ty.isForall then rD := some d
  let some zh := zhD | throwError "fv_ret_names: no Nat → BitVec 256 result"
  let some fd := fD | throwError "fv_ret_names: no Flags result"
  let some md := mD | throwError "fv_ret_names: no Memory result"
  let some fr := frD | throwError "fv_ret_names: no MemFrame hypothesis"
  let some rr := rD | throwError "fv_ret_names: no relation hypothesis"
  unless w64.size ≥ 2 && bv128.size ≥ 2 do throwError "fv_ret_names: missing Nat → W64 / BitVec 128 results"
  let pairs : Array (LocalDecl × Name) := #[
    (w64[w64.size - 2]!, ids[0]!.getId), (fd, ids[1]!.getId), (bv128[bv128.size - 2]!, ids[2]!.getId),
    (bv128[bv128.size - 1]!, ids[3]!.getId), (md, ids[4]!.getId), (zh, ids[5]!.getId), (w64[w64.size - 1]!, ids[6]!.getId),
    (fr, ids[8]!.getId), (rr, ids[9]!.getId)]
  for (d, n) in pairs do
    lctx := lctx.setUserName d.fvarId n
  if let some pr := prD then lctx := lctx.setUserName pr.fvarId ids[7]!.getId
  let g' ← mkFreshExprMVarAt lctx decl.localInstances decl.type
  g.assign g'
  replaceMainGoal [g'.mvarId!]

end Fv256.GrabRet
