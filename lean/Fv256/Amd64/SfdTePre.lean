import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdEnv

/-!
# `strconv.toError(fn, s, base, bitSize, err)` for `err == ErrSyntax` (amd64), as a callee of `strconv.ParseUint`

`ParseUint` calls `toError("ParseUint", s, 10, 64, err)` when the internal parser fails; for a syntax failure the
result is `&NumError{Func: fn, Num: cloneString(s), Err: strconv.ErrSyntax}` (a freshly allocated object, the
string copied by `mallocgc` + `memmove`).  The runtime calls are `runtime.ifaceeq` (the comparison
`err == ErrSyntax`, interface-model contract), `runtime.mallocgc`, `runtime.memmove`, `runtime.newobject` and the
write barriers (live contracts, all threaded through one `RtInv`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.Amd64.SfdEnv

namespace Fv256.Amd64.SfdToError

abbrev te : Nat := segAddr Extracted.program "strconv.toError"



open Fv256.C in
def TePre (R : RtInv) (R2 : IfaceModel) (T : Nat) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = fp ∧ s.regs 3 = fl ∧ s.regs 1 = sp ∧ s.regs 7 = sl ∧
  s.regs 9 = BitVec.ofNat 64 errItab ∧ s.regs 10 = BitVec.ofNat 64 synConst ∧
  1 ≤ sl.toNat ∧ sl.toNat < 2 ^ 40 ∧
  StackGuardOK s 4192 ∧ StackWritable s 4192 72 ∧ (s.regs 4).toNat % 8 = 0 ∧
  s.mem.readLE numErrType 8 = 48 ∧ s.mem.readLE (numErrType + 8) 8 ≠ 0 ∧ s.mem.accessible numErrType 16 false = true ∧
  s.mem.accessible errItab 16 false = true ∧ s.mem.accessible synConst 8 false = true ∧
  R2.depth ≤ 4096 ∧ CallerOK R2 s 96 72 ∧
  Outside ((s.regs 4).toNat - 4192) 4264 R.rt ∧
  R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)]) ∧
  blockSize sl.toNat true + blockSize 48 false ≤ b ∧
  s.mem.readLE (errItab + 8) 8 = T ∧ R2.IsType T ∧ isRegularMemory s.mem T = true ∧ isDirectIface s.mem T = false ∧
  tySize s.mem T = 8 ∧
  Outside errItab 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside synConst 8 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside strconvErrSyntax 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside wbFlag 4 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside numErrType 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  (∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt) ∧ (∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv) ∧
  Outside numErrType 16 R.rt ∧ Outside wbFlag 4 R.rt ∧ Outside strconvErrSyntax 16 R.rt ∧
  R.ok (Extracted.program.contractAddr "runtime.mallocgc") [sl.toNat, 0, 0] ∧
  R.ok (Extracted.program.contractAddr "runtime.newobject") [numErrType] ∧
  (∀ q, R.ok (Extracted.program.contractAddr "runtime.memmove") [q, sp.toNat, sl.toNat]) ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  s.mem.accessible sp.toNat sl.toNat false = true ∧ sp.toNat + sl.toNat ≤ 2 ^ 48 ∧
  (sp.toNat + sl.toNat ≤ (s.regs 4).toNat - 4192 ∨ (s.regs 4).toNat + 72 ≤ sp.toNat) ∧
  Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4192) 4264 ∧
  Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
  (∀ r ∈ R.rt, 0 < r.1) ∧
  Outside numErrType 16 R2.priv ∧ Outside wbFlag 4 R2.priv ∧ Outside strconvErrSyntax 16 R2.priv ∧
  s.mem.accessible wbFlag 4 false = true ∧ s.mem.accessible strconvErrSyntax 16 false = true ∧
  (Outside sp.toNat sl.toNat R.rt ∨ InRanges sp.toNat sl.toNat L) ∧ Outside sp.toNat sl.toNat R2.priv


/-- the facts about the fresh error object `t` (a `*strconv.NumError`) and the fresh copy `q` of the string `(sp, sl)` that
`strconv.toError` builds for an `ErrSyntax` failure with function name `(fp, fl)`: `Func = (fp, fl)`, `Num = (q, sl)`,
`Err = strconv.ErrSyntax` (the variable's value in `s.mem`), both objects fresh and live in `s'`. -/
def TeObj (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) (q t : Nat) : Prop :=
  InRanges q (blockSize sl.toNat true) R.rt ∧ InRanges t (blockSize 48 false) R.rt ∧
  ApartAll q (blockSize sl.toNat true) L ∧ ApartAll t (blockSize 48 false) (L ++ [(q, q + blockSize sl.toNat true)]) ∧
  s'.mem.readLE t 8 = fp.toNat ∧ s'.mem.readLE (t + 8) 8 = fl.toNat ∧ s'.mem.readLE (t + 16) 8 = q ∧
  s'.mem.readLE (t + 24) 8 = sl.toNat ∧ s'.mem.readLE (t + 32) 8 = s.mem.readLE strconvErrSyntax 8 ∧
  s'.mem.readLE (t + 40) 8 = s.mem.readLE (strconvErrSyntax + 8) 8 ∧
  (∀ k, k < sl.toNat → s'.mem.readLE (q + k) 1 = s.mem.readLE (sp.toNat + k) 1) ∧
  R.inv (b - blockSize sl.toNat true - blockSize 48 false)
    (L ++ [(q, q + blockSize sl.toNat true), (t, t + blockSize 48 false)]) (s.regs 14).toNat
    (view R.rt (L ++ [(q, q + blockSize sl.toNat true), (t, t + blockSize 48 false)]) s'.mem)

def TeErr (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) : Prop :=
  ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 numErrItab ∧ s'.regs 3 = t ∧ TeObj R b L fp fl sp sl s s' q t.toNat

open Fv256.C in
def TePost (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) : Prop :=
  Kept s s' ∧ TeErr R b L fp fl sp sl s s' ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)])

theorem inRanges_fields {t : Nat} {rs rs' : List (Nat × Nat)} (h : InRanges t 48 rs) (hs : ∀ r ∈ rs, r ∈ rs') :
    InRanges t 8 rs' ∧ InRanges (t + 8) 8 rs' ∧ InRanges (t + 16) 8 rs' ∧ InRanges (t + 24) 8 rs' ∧
      InRanges (t + 32) 8 rs' ∧ InRanges (t + 40) 8 rs' := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have hr' := hs r hr
  exact ⟨⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩,
    ⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩⟩

theorem frame_trans {m m' m'' : Janus.Arm64.Memory} {rs rs' : List (Nat × Nat)} (h : MemFrame m m' rs)
    (h' : MemFrame m' m'' rs') (sub : ∀ a n, Outside a n rs → Outside a n rs') : MemFrame m m'' rs :=
  h.trans h' (fun a n ho => ⟨ho, sub a n ho⟩)

theorem inRanges16_lo {a : Nat} {rs : List (Nat × Nat)} (h : InRanges a 16 rs) : InRanges a 8 rs := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, hr, by omega, by omega⟩

theorem inRanges16_hi {a : Nat} {rs : List (Nat × Nat)} (h : InRanges a 16 rs) : InRanges (a + 8) 8 rs := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, hr, by omega, by omega⟩

theorem frame_writeLE_rt {m m' : Janus.Arm64.Memory} {rt priv : List (Nat × Nat)} {w : Nat × Nat} {a k : Nat} (v : Nat)
    (h : MemFrame m m' (rt ++ priv ++ [w])) (hin : InRanges a k rt) :
    MemFrame m (m'.writeLE a k v) (rt ++ priv ++ [w]) :=
  h.writeLE_inRanges v (InRanges.of_subset hin (by intro r hr; simp [List.mem_append, hr]))

/-- discharge the coverage side condition of a callee frame in `te_frame` -/
macro "te_sub" : tactic => `(tactic|
  (intro a n h
   revert h
   simp only [Janus.outside_cons, Janus.outside_nil, Janus.outside_append, and_true, and_imp]
   intros
   first
   | (janus_clear_irrel
      try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
      repeat' apply And.intro
      all_goals first | (with_reducible assumption) | omega)
   | (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
      repeat' apply And.intro
      all_goals first | (with_reducible assumption) | omega)
   | (janus_apart_facts
      try simp only [Janus.Apart] at *
      janus_clear_irrel2
      try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
      repeat' apply And.intro
      all_goals first | omega | (with_reducible assumption))))

/-- `MemFrame m₀ m rs` for `rs = rt ++ priv ++ [window]`: stores into the window or into objects given by
`InRanges` facts over the whole list, callee frames from the context. -/
macro "te_frame" : tactic => `(tactic|
  (repeat' (first
    | (with_reducible exact Janus.MemFrame.refl _ _)
    | (refine frame_writeLE_rt _ ?_ (by first | assumption | exact inRanges16_lo (by assumption) | exact inRanges16_hi (by assumption)))
    | (refine Janus.MemFrame.writeLE ?_ _ (List.mem_append_right _ (List.mem_singleton_self _)) (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega) (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega))
    | (refine frame_trans ?_ (by assumption) ?_))
   all_goals first | (te_sub) | skip))

theorem mem3 {α : Type} {r w : α} {a b : List α} (h : r ∈ a ++ b ++ [w]) : r ∈ a ∨ r ∈ b ∨ r = w := by
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem blockSize48 : blockSize 48 false = 48 := by decide

theorem inRanges_last {a n : Nat} {l : List (Nat × Nat)} {r : Nat × Nat} (h : r.1 ≤ a ∧ a + n ≤ r.2) :
    InRanges a n (l ++ [r]) := ⟨r, by simp, h.1, h.2⟩

theorem inRanges_pen {a n : Nat} {l : List (Nat × Nat)} {r r2 : Nat × Nat} (h : r.1 ≤ a ∧ a + n ≤ r.2) :
    InRanges a n (l ++ [r] ++ [r2]) := ⟨r, by simp, h.1, h.2⟩

/-- `omega` after dropping the hypotheses unrelated to the goal (the contexts carry giant memory terms) -/
macro "te_omega" : tactic => `(tactic| first | (janus_clear_irrel; omega) | omega)

/-- the atomic side conditions of the `te_walk` rewrite rules (cheap structured steps first; `omega` last) -/
macro "te_atom" : tactic => `(tactic| first
  | with_reducible assumption
  | (exact Janus.Outside.of_sub (by with_reducible assumption) (by te_omega) (by te_omega))
  | (exact Janus.InRanges.sub (by with_reducible assumption) (by te_omega) (by te_omega))
  | te_omega)

/-- the side conditions of the `te_walk` rewrite rules -/
macro "te_disch" : tactic => `(tactic| first
  | with_reducible assumption
  | trivial
  | exact True.intro
  | (exact inRanges_last ⟨by te_omega, by te_omega⟩)
  | (exact inRanges_pen ⟨by te_omega, by te_omega⟩)
  | (simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
     repeat' apply And.intro
     all_goals te_atom)
  | te_omega)

macro "te_close" : tactic => `(tactic| first
  | with_reducible exact Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)
  | (rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; with_reducible exact Nat.mod_eq_of_lt (BitVec.isLt _))
  | skip)

theorem inRanges_last2 {a n : Nat} {l : List (Nat × Nat)} {r1 r : Nat × Nat} (h : r.1 ≤ a ∧ a + n ≤ r.2) :
    InRanges a n (l ++ [r1, r]) := ⟨r, by simp, h.1, h.2⟩

theorem append_two {α : Type} (l : List α) (a b : α) : l ++ [a, b] = l ++ [a] ++ [b] := by simp

open Lean Elab Tactic Meta in
/-- unfold every `Apart` hypothesis of the context into its disjunction (for the `omega` side conditions) -/
elab "te_unfold_apart" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Janus.Apart then
      let h := mkIdent d.userName
      evalTactic (← `(tactic| simp only [Janus.Apart] at $h:ident))

open Lean Elab Tactic Meta in
/-- rewrite memory reads through stores and through the `LiveFrame`/`MemFrame` facts of the context -/
elab "te_walk" : tactic => withMainContext do
  let mut rules : Array (TSyntax `term) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if d.userName == `hF then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Janus.LiveFrame && (ty.getArg! 3).isAppOf ``List.nil then
      let h ← Term.exprToSyntax d.toExpr
      rules := rules.push (← `(Janus.LiveFrame.readLE_nil $h))
    else if ty.isAppOf ``Janus.LiveFrame || ty.isAppOf ``Janus.MemFrame then
      let h ← Term.exprToSyntax d.toExpr
      rules := rules.push (← `(($h).readLE))
  evalTactic (← `(tactic| try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]))
  evalTactic (← `(tactic| simp (disch := te_disch) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Nat.reduceAdd, $[$rules:term],*]))
  evalTactic (← `(tactic| te_close))

open Lean Elab Tactic Meta in
/-- give the (possibly shadowed) hypothesis `fv` the fresh name `n` -/
def teRenameFV (fv : FVarId) (n : Name) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let lctx := (← getLCtx).setUserName fv n
    let ng ← mkFreshExprMVarAt lctx (← getLocalInstances) (← g.getType)
    g.assign ng
    replaceMainGoal [ng.mvarId!]


/-- the `i`-th argument of an application, or a dummy constant when there is none -/
def targ (e : Lean.Expr) (i : Nat) : Lean.Expr := (e.getAppArgs[i]?).getD (Lean.mkConst ``Nat)

open Lean Elab Tactic Meta in
/-- Name, by the content of their types (not by position), the facts of the `mallocgc` call's postcondition that the
`toError` proof uses: `q` (the fresh string), `m2` (memory after the call), `hLF`/`hMF` (its live and memory frames),
`hInR` (the block lies in the runtime ranges), `hQsl` (`sl ≤ blockSize sl`) and the four `Apart` facts of the block
against the stack window, `numErrType`, `wbFlag` and `strconvErrSyntax`. -/
elab "te_grab" : tactic => withMainContext do
  let mut found : Array (Name × FVarId) := #[]
  let mut mem2 : Option Expr := none
  -- first pass: the live frame whose live list is the variable `L` (not `L ++ _`)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Janus.LiveFrame && (targ ty 2).isFVar && (targ ty 3).isAppOf ``List.nil && mem2.isNone then
      mem2 := some (targ ty 1)
      found := found.push (`hLF, d.fvarId)
  let some m2e := mem2 | throwError "te_grab: no LiveFrame over the live variable"
  let mut qfv : Option FVarId := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Janus.MemFrame && ty.getAppNumArgs == 3 && (← isDefEq (targ ty 1) m2e) && !(found.any (·.1 == `hMF)) then
      found := found.push (`hMF, d.fvarId)
    else if ty.isAppOf ``Janus.InRanges && (targ ty 1).isAppOf ``Janus.Contracts.blockSize then
      found := found.push (`hInR, d.fvarId)
      match (targ ty 0) with
      | .app _ (.fvar q) => qfv := some q
      | _ => pure ()
    else if ty.isAppOf ``LE.le && (targ ty 3).isAppOf ``Janus.Contracts.blockSize then
      found := found.push (`hQsl, d.fvarId)
    else if ty.isAppOf ``Janus.Apart && (targ ty 2).isApp then
      let a := targ ty 0
      let b := targ ty 2
      if b.isAppOf ``BitVec.toNat then
        if a.isAppOf ``HSub.hSub then found := found.push (`hAw, d.fvarId)
        else if a.isConstOf `Fv256.I.numErrType || a.isConstOf `Fv256.Amd64.SfdEnv.numErrType then found := found.push (`hAn, d.fvarId)
        else if a.isConstOf `Fv256.I.wbFlag || a.isConstOf `Fv256.Amd64.SfdEnv.wbFlag then found := found.push (`hAwb, d.fvarId)
        else if a.isConstOf `Fv256.I.strconvErrSyntax || a.isConstOf `Fv256.Amd64.SfdEnv.strconvErrSyntax then found := found.push (`hAe, d.fvarId)
  for n in [`hLF, `hMF, `hInR, `hQsl, `hAw, `hAn, `hAwb, `hAe] do
    unless found.any (·.1 == n) do throwError "te_grab: no hypothesis for {n}"
  for (n, fv) in found do
    teRenameFV fv n
  if let some q := qfv then teRenameFV q `q
  if m2e.isFVar then teRenameFV m2e.fvarId! `m2

open Lean Elab Tactic Meta in
/-- `te_walk` at the two hypotheses that test the write-barrier flag address (they must agree): close the goal
when one is `P` and the other `¬P` after the rewriting (syntactically, up to reducible unfolding) -/
elab "te_flags" : tactic => withMainContext do
  let mut rules : Array (TSyntax `term) := #[]
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Janus.LiveFrame && (ty.getArg! 3).isAppOf ``List.nil then
      let h ← Term.exprToSyntax d.toExpr
      rules := rules.push (← `(Janus.LiveFrame.readLE_nil $h))
    else if ty.isAppOf ``Janus.LiveFrame || ty.isAppOf ``Janus.MemFrame then
      let h ← Term.exprToSyntax d.toExpr
      rules := rules.push (← `(($h).readLE))
    else if (ty.find? fun e => e.isRawNatLit && e.rawNatLit? == some 6156064).isSome &&
        (ty.isAppOf ``Eq || ty.isAppOf ``Not) then
      hs := hs.push d.fvarId
  evalTactic (← `(tactic| try (have teflagw := (by with_reducible assumption : Janus.Outside 6156064 4 [(_, _)]); simp only [Janus.outside_cons, Janus.outside_nil, and_true] at teflagw)))
  let mut names : Array Name := #[]
  let mut k := 0
  for fv in hs do
    let n := Name.mkSimple s!"teflag{k}"
    teRenameFV fv n
    names := names.push n
    k := k + 1
  for n in names do
    let h := mkIdent n
    evalTactic (← `(tactic| try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff] at $h:ident))
    evalTactic (← `(tactic| try simp (disch := te_disch) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Nat.reduceAdd, $[$rules:term],*] at $h:ident))
  if (← System.FilePath.pathExists "/srv/fv-uint256-wi/build/out/debug_flags") then
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOf ``Janus.LiveFrame || ty.isAppOf ``Janus.MemFrame then
        let a ← Meta.ppExpr (ty.getArg! 0)
        let b ← Meta.ppExpr (ty.getArg! 1)
        let rs ← Meta.ppExpr (ty.getArg! 2)
        let h ← IO.FS.Handle.mk "/srv/fv-uint256-wi/build/out/marks.txt" IO.FS.Mode.append
        h.putStrLn s!"FRAME {ty.getAppFn.constName!} from={(toString a).take 120} to={(toString b).take 40} rs={(toString rs).take 300}"
        h.flush
    for n in names do
      let str ← withMainContext do
        let d ← getLocalDeclFromUserName n
        let ty ← instantiateMVars d.type
        pure (toString (← Meta.ppExpr ty))
      let h ← IO.FS.Handle.mk "/srv/fv-uint256-wi/build/out/marks.txt" IO.FS.Mode.append
      h.putStrLn s!"FLAG {n}: {str.take 800}"
      h.flush
  for a in names do
    for b in names do
      if a != b then
        let ia := mkIdent a
        let ib := mkIdent b
        evalTactic (← `(tactic| try (with_reducible exact absurd $ia $ib)))
        if (← getGoals).isEmpty then return

open Lean Elab Tactic Meta in
/-- `te_walk` through the stores only (no frame facts) -/
elab "te_walk0" : tactic => withMainContext do
  evalTactic (← `(tactic| try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]))
  evalTactic (← `(tactic| simp (disch := te_disch) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Nat.reduceAdd]))

/-- the invariant for the finished object: the stores into the fresh object do not change the view -/
macro "te_inv" : tactic => `(tactic|
  (try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
   rw [blockSize48, append_two]
   simp (disch := te_disch) only [Janus.Contracts.view_writeLE_live]
   janus_assumption))

theorem te_post_intro {R : RtInv} {R2 : IfaceModel} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64} {s s' : State}
    (hk : Fv256.C.Kept s s')
    (hF : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)]))
    (he : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)]) →
      TeErr R b L fp fl sp sl s s') : TePost R R2 b L fp fl sp sl s s' := ⟨hk, he hF, hF⟩

end Fv256.Amd64.SfdToError
