import SvyTools
import Lean
open Lean Elab Command
namespace Fv256.T
-- (evalExpr / evalTerm / evalConst are `unsafe` and need the banned `unsafe`; elabCommandTopLevel is the safe route to run built syntax)
elab "sneak3" : command => do
  let stx ← `(command| def zzz := 1)
  Lean.Elab.Command.elabCommandTopLevel stx
end Fv256.T
#lint_io
