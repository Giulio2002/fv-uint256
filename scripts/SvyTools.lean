import Lean
open Lean Elab Command Meta

/-! Survey tooling (not part of the release tree).  Importing this module makes every `theorem` declaration elaborate
with its proof replaced by `sorry` (statements are still fully elaborated), and provides `#spec_closure`. -/

namespace SvyTools

private def mkSorryVal : CommandElabM Syntax := do
  let env ← getEnv
  match Parser.runParserCategory env `command "theorem svyTmp : True := sorry" with
  | .ok stx => return stx[1][3]    -- declaration -> theorem -> declVal
  | .error e => throwError e

@[command_elab Lean.Parser.Command.declaration] def elabSkipProofs : CommandElab := fun stx => do
  let k := stx[1]
  unless k.isOfKind ``Parser.Command.theorem do throwUnsupportedSyntax
  let v := k[3]
  unless v.isOfKind ``Parser.Command.declValSimple do throwUnsupportedSyntax
  -- already `sorry`?
  if v[1].isOfKind ``Parser.Term.sorry then throwUnsupportedSyntax
  let sv ← mkSorryVal
  let k' := k.setArg 3 sv
  elabCommand (stx.setArg 1 k')


def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- `#spec_closure t1 t2 ..`: constants of modules `Fv256*` (or of the current file) reachable from the TYPES of the given
theorems, through definitions (types and values) but not through theorem types/values.  Theorems reached are reported with kind
`thm` and are NOT traversed. One line per constant: `@@C <const> <module> <kind> <parent> <declranges>`.  `@@S <thm>` lines list the roots. -/
elab "#spec_closure " ids:ident+ : command => do
  let env ← getEnv
  let modOf (c : Name) : String :=
    match env.getModuleIdxFor? c with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => "<cur>"
  let isFv (m : String) : Bool := m == "<cur>" || m.startsWith "Fv256"
  let seen ← IO.mkRef (({} : NameSet))
  let out ← IO.mkRef (#[] : Array String)
  let queue ← IO.mkRef (#[] : Array (Name × Name))
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    out.modify (·.push s!"@@S {n}")
    let some ci := env.find? n | throwError "unknown {n}"
    for c in ci.type.getUsedConstants do queue.modify (·.push (c, n))
  repeat
    let q ← queue.get
    if q.isEmpty then break
    let (c, par) := q.back!
    queue.set q.pop
    if (← seen.get).contains c then continue
    seen.modify (·.insert c)
    let m := modOf c
    unless isFv m do continue
    let some ci := env.find? c | continue
    let rng ← liftCoreM <| findDeclarationRanges? c
    let rs := match rng with
      | some r => s!"{r.range.pos.line}:{r.range.pos.column}-{r.range.endPos.line}:{r.range.endPos.column}"
      | none => "-"
    out.modify (·.push s!"@@C {c} {m} {kindOf ci} {par} {rs}")
    match ci with
    | .thmInfo _ => pure ()
    | _ =>
      for d in ci.type.getUsedConstants do queue.modify (·.push (d, c))
      match ci.value? with
      | some v => for d in v.getUsedConstants do queue.modify (·.push (d, c))
      | none => pure ()
      match ci with
      | .inductInfo i => for ct in i.ctors do queue.modify (·.push (ct, c))
      | _ => pure ()
  logInfo ("\n" ++ "\n".intercalate (← out.get).toList)


/-- `#lint_io`: LEAN-LEVEL second-layer lint over every constant defined in an `Fv256*` module of the current environment (the module's
transitive imports plus the current file).  Findings (one `@@IO` line each): a constant whose TYPE mentions `IO`/`EIO`/`BaseIO`/`BaseIO`-family
or whose VALUE references an IO / system primitive (any constant in the `IO`, `EIO`, `BaseIO`, `System`, `ST`, `Task`, `IO.FS`, `IO.Process`
namespaces, or `Lean.Elab.Command.liftIO`/`Lean.liftIO`/`IO.toEIO`-style lifts), and any `@[init]` / `initialize` / `builtin_initialize`
declaration (`getInitFnNameFor?` / `isIOUnitInitFn` / builtin variants).  Resolution is by elaborated constant, so `open IO` aliasing is irrelevant.
Theorem values are proof terms and are not scanned (their tactic blocks are covered by scripts/lint_source.py). Last line: `@@IOCOUNT <n>`. -/
private def ioRoots : List Name := [`IO, `EIO, `BaseIO, `System, `ST, `Task, `IO.FS, `IO.Process, `ByteArray.IO, `Lean.liftIO, `liftIO,
  `Lean.Elab.Command.liftIO, `Lean.Elab.Term.liftIO, `Lean.Elab.Tactic.liftIO, `Lean.Meta.liftIO, `Lean.Core.liftIO]

private def isIOName (n : Name) : Bool :=
  ioRoots.any (fun r => r.isPrefixOf n) || (n.getRoot == `IO)

/-- value-side: `elab`/`elab_rules` bodies legitimately mention the monad plumbing `IO.RealWorld` / `IO.Error` (the representation of
`CommandElabM` etc.) and the bare type constant `IO` / `EIO` / `BaseIO` / `ST` as monad TYPES; every other IO / System / liftIO reference in a VALUE
is a primitive and is rejected (this includes `IO.mkRef` / `ST.Ref` / `ST.Prim.*` cells, `IO.FS`, `IO.Process`, `IO.getEnv`, clocks, `System.*`,
and the `toEIO`/`liftIO` lifts). -/
private def ioPlumbing : List Name := [`IO.RealWorld, `IO.Error, `IO, `EIO, `BaseIO, `ST, `IO.instMonadLiftSTRealWorldBaseIO,
  `instMonadEIO, `instMonadBaseIO, `instMonadST, `instMonadLiftSTRealWorldBaseIO]

/-- constants that run or elaborate syntax / code that is built at elaboration time: an `elab` that assembles `#eval ...` from string pieces,
parses it with `runParserCategory` and runs it through `elabCommand` executes arbitrary code while every source-level token lint stays green
(red-team N13 LA1).  Any VALUE in an Fv256 module referencing one of these is rejected. -/
private def execPrims : List Name :=
  [`Lean.Parser.runParserCategory, `Lean.Parser.parseCommand, `Lean.Parser.parseHeader, `Lean.Parser.parseTactic?, `Lean.Elab.Command.elabCommand,
   `Lean.Elab.Command.elabCommandTopLevel, `Lean.Elab.Command.runLinters, `Lean.Elab.Term.evalTerm, `Lean.Elab.Term.evalTermCheck?,
   `Lean.Meta.evalExpr, `Lean.Meta.evalExpr', `Lean.Environment.evalConst, `Lean.Environment.evalConstCheck, `Lean.evalConst, `Lean.evalConstCheck,
   `Lean.evalDecl, `Lean.Elab.runFrontend, `Lean.Elab.IO.processCommands, `Lean.Elab.Frontend, `Lean.Elab.processHeader, `Lean.Elab.parseImports,
   `Lean.importModules, `Lean.withImporting, `Lean.Elab.Command.elabEvalCoreUnsafe, `Lean.Elab.Command.elabEvalUnsafe, `Lean.Elab.Command.elabRunCmd,
   `Lean.Elab.Term.elabRunElab, `Lean.Elab.Tactic.evalRunTac, `Lean.loadExts, `Lean.runModInit, `Lean.runInit, `Lean.registerInitAttr,
   `Lean.registerBuiltinAttribute, `Lean.addAndCompile, `Lean.compileDecl, `Lean.compileDecls, `Lean.IR.addBoxedVersion]

private def isExecPrim (n : Name) : Bool := execPrims.any (fun r => r == n)

private def isIOPrim (n : Name) : Bool :=
  isIOName n && !ioPlumbing.any (fun r => r == n) && !(`IO.RealWorld).isPrefixOf n && !(`IO.Error).isPrefixOf n

elab "#lint_io" : command => do
  let env ← getEnv
  let mut out : Array String := #[]
  let mut count := 0
  let isFvMod (m : Name) : Bool := m.getRoot == `Fv256
  let check (c : Name) (ci : ConstantInfo) (modName : String) : CommandElabM (Array String) := do
    let mut r : Array String := #[]
    for d in ci.type.getUsedConstants do
      if isIOName d then r := r.push s!"@@IO {c} {modName} type-mentions {d}"
      else if isExecPrim d then r := r.push s!"@@IO {c} {modName} type-mentions-exec {d}"
    match ci with
    | .thmInfo _ => pure ()
    | _ =>
      match ci.value? with
      | some v => for d in v.getUsedConstants do
          if isIOPrim d then r := r.push s!"@@IO {c} {modName} value-references {d}"
          else if isExecPrim d then r := r.push s!"@@IO {c} {modName} value-references-exec {d}"
      | none => pure ()
    if (Lean.getInitFnNameFor? env c).isSome || Lean.isIOUnitInitFn env c || (Lean.getBuiltinInitFnNameFor? env c).isSome
        || Lean.isIOUnitBuiltinInitFn env c then
      r := r.push s!"@@IO {c} {modName} init-declaration"
    return r
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if isFvMod m then
      for c in env.header.moduleData[i]!.constNames do
        if let some ci := env.find? c then
          out := out ++ (← check c ci m.toString)
          count := count + 1
  -- the current file's own declarations
  for (c, ci) in env.constants.map₂.toList do
    out := out ++ (← check c ci "<cur>")
    count := count + 1
  logInfo ("\n" ++ "\n".intercalate out.toList ++ s!"\n@@IOCOUNT {count}")

end SvyTools
