import SvyTools
open Lean Elab Command
namespace Fv256.T
def pure1 : Nat := 1
elab "goodcmd" : command => do logInfo "hello"
theorem t : pure1 = 1 := rfl
end Fv256.T
#lint_io
