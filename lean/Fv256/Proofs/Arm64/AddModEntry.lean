import Fv256.Proofs.Arm64.AddModProg
namespace Fv256.Arm64.AddModProg
/-- entry of `(*Int).AddMod` in the library program -/
def entry : Nat := 0xba410
theorem entry_eq : entry = Janus.Tactic.segAddr program "github.com/holiman/uint256.(*Int).AddMod" := by decide
end Fv256.Arm64.AddModProg
