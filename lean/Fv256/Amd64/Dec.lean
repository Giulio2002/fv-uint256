import Extracted
import Fv256.Spec
import Fv256.SpecE

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Dec

theorem probe : Extracted.entry = Extracted.entry := rfl

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (fun s => StackWritable s 0 8) (fun _ _ => True) := by
  sorry

end Fv256.Amd64.Dec
