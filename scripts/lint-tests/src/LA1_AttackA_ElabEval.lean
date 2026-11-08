import SvyTools
import Lean
open Lean Elab Command Term Meta

namespace Fv256.AttackA
/-- RT13 LA1: `#eval` assembled from string pieces; IO runs at elaboration; no forbidden token, no IO-named constant in the value. -/
elab "sneak" : command => do
  let env ← getEnv
  let s := "#ev" ++ "al (do IO.printl" ++ "n s!\"HOME={(← IO.get" ++ "Env \"HOME\")} clock={← IO.monoNa" ++ "nosNow}\" : IO Unit)"
  match Parser.runParserCategory env `command s with
  | .ok stx => elabCommand stx
  | .error e => throwError e
sneak
end Fv256.AttackA
