import Janus

/-!
# `fv_ret_names_a64`: content-based names for the results of an arm64 `ICallContract` after `janus_run … calls [h]`

Names the inaccessible results of the LAST icall by what they are (their types), never by position:
`junk : Nat → W64`, `f : Flags`, `v : Nat → BitVec 128`, `m : Memory`, `ex : Option (Nat × Nat)`, `ep : Nat → Bool`,
`hkeep` (the `keep` hypothesis, a `∀ r ∈ _`), `hpr` (mentions `RtPreserves`), `hfr` (the last `MemFrame`), `hR` (the last other
proposition).  Replaces a positional `rename_i junk f v m ex ep hkeep hfr hR`.  arm64 twin of `Fv256.GrabRet.fv_ret_names`.
-/

namespace Fv256.GrabRetA64

open Lean Elab Tactic Meta

elab "fv_ret_names_a64 " a0:ident a1:ident a2:ident a3:ident a4:ident a5:ident a6:ident a7:ident a8:ident a9:ident : tactic => do
  let ids : Array Ident := #[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  -- order of the names: junk f v m ex ep hkeep hpr hfr hR
  let g ← getMainGoal
  let decl ← g.getDecl
  let mut lctx := decl.lctx
  let mut w64 : Option LocalDecl := none
  let mut bv128 : Option LocalDecl := none
  let mut epD : Option LocalDecl := none
  let mut exD : Option LocalDecl := none
  let mut fD : Option LocalDecl := none
  let mut mD : Option LocalDecl := none
  let mut prD : Option LocalDecl := none
  let mut keepD : Option LocalDecl := none
  let mut frD : Option LocalDecl := none
  let mut rD : Option LocalDecl := none
  for d in decl.lctx do
    if d.isImplementationDetail || !d.userName.hasMacroScopes then continue
    let ty ← instantiateMVars d.type
    if ty.isForall && (← isProp ty) then keepD := some d
    else if ty.isForall && ty.bindingDomain!.isConstOf ``Nat then
      let b ← whnfR ty.bindingBody!
      if b.isAppOfArity ``BitVec 1 && (b.getArg! 0).nat? == some 64 then w64 := some d
      else if b.isAppOfArity ``BitVec 1 && (b.getArg! 0).nat? == some 128 then bv128 := some d
      else if b.isConstOf ``Bool then epD := some d
    else if ty.getAppFn.isConstOf ``Option then exD := some d
    else if ty.getAppFn.isConstOf ``Janus.Arm64.Flags then fD := some d
    else if ty.getAppFn.isConstOf ``Janus.Arm64.Memory then mD := some d
    else if (ty.find? fun e => e.isConstOf `Janus.Contracts.ICall.RtPreserves).isSome then prD := some d
    else if ty.isAppOf `Janus.MemFrame then frD := some d
    else if (← isProp ty) && !ty.isForall && ty.getAppFn.isFVar then rD := some d
  let some jd := w64 | throwError "fv_ret_names_a64: no Nat → W64 result"
  let some fd := fD | throwError "fv_ret_names_a64: no Flags result"
  let some vd := bv128 | throwError "fv_ret_names_a64: no Nat → BitVec 128 result"
  let some md := mD | throwError "fv_ret_names_a64: no Memory result"
  let some exd := exD | throwError "fv_ret_names_a64: no Option result"
  let some epd := epD | throwError "fv_ret_names_a64: no Nat → Bool result"
  let some fr := frD | throwError "fv_ret_names_a64: no MemFrame hypothesis"
  let some rr := rD | throwError "fv_ret_names_a64: no relation hypothesis"
  let pairs : Array (LocalDecl × Name) := #[
    (jd, ids[0]!.getId), (fd, ids[1]!.getId), (vd, ids[2]!.getId), (md, ids[3]!.getId), (exd, ids[4]!.getId),
    (epd, ids[5]!.getId), (fr, ids[8]!.getId), (rr, ids[9]!.getId)]
  for (d, n) in pairs do
    lctx := lctx.setUserName d.fvarId n
  if let some k := keepD then lctx := lctx.setUserName k.fvarId ids[6]!.getId
  if let some pr := prD then lctx := lctx.setUserName pr.fvarId ids[7]!.getId
  let g' ← mkFreshExprMVarAt lctx decl.localInstances decl.type
  g.assign g'
  replaceMainGoal [g'.mvarId!]

end Fv256.GrabRetA64
