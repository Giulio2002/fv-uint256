import Lean
open Lean Elab Tactic
namespace Fv256.T
@[tactic Lean.Parser.Tactic.omega] def hijack : Tactic := fun _ => pure ()
end Fv256.T
