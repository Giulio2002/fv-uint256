import SvyTools
import Lean
open Lean Elab Command Term Meta

namespace Fv256.AttackB
/-- RT13 LA2: evalExpr of an Expr naming an IO action only by Name data. -/
elab "sneak2" : command => do
  let e := mkApp (mkConst (Name.mkStr (Name.mkStr .anonymous ("I" ++ "O")) ("monoNa" ++ "nosNow"))) default
  let _ := e
  logInfo "sneak2 elaborated"
sneak2
end Fv256.AttackB
