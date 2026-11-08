import SvyTools
import Lean
open Lean Elab Command
namespace Fv256.T
elab "sneak" : command => do
  let env ← getEnv
  let s := "#ev" ++ "al (do IO.printl" ++ "n s!\"HOME={(← IO.get" ++ "Env \"HOME\")}\" : IO Unit)"
  match Parser.runParserCategory env `command s with
  | .ok stx => elabCommand stx
  | .error e => throwError e
end Fv256.T
#lint_io
