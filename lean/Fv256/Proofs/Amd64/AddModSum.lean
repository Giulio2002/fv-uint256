import Fv256.Proofs.Common.AddModProg
import Fv256.Proofs.Amd64.AddModSpecS
import Fv256.Proofs.Amd64.AddModFast
import Fv256.Proofs.Amd64.AddModComp

/-!
# `AddMod` as a library summary over `AddModProg` (Extracted-free)

`addmod_summary`: for every state at the entry of `(*Int).AddMod` satisfying `AddPre`, the call returns (no fault, no panic) and
`AddPost` holds.  Consumers (`AddMod.correctness`, FV-D's `IAddMod`) transfer it with `Fv256.CodeIn.lib_summary`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModSum

abbrev addmodEntry : Nat := Fv256.Amd64.AddModFast.addmodEntry

theorem addmod_summary :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s) AddPost := by
  intro s hpc hpre
  by_cases hc : AddCase s
  · exact Fv256.Amd64.AddModFast.fast s hpc ⟨hpre, hc⟩
  · exact Fv256.Amd64.AddModComp.gen2 s hpc ⟨hpre, hc⟩

end Fv256.Amd64.AddModSum
