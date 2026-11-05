import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false)
      (fun s s' => ((val256 s.mem x.toNat = 0 → (s'.regs 0).toNat = 0) ∧
        (val256 s.mem x.toNat ≠ 0 → 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧
          val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)))) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hx, hx'⟩
  janus_intro hs
  janus_data hd [hw]
  janus_run
  all_goals (trace_state; sorry)

end Fv256.Arm64.Log10
