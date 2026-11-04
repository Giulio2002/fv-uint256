import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.L10Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem zero (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE x.toNat 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 24) 8 = 0)
      (fun s s' => (s'.regs 0).toNat = 0) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz0, hz1, hz2, hz3⟩
  janus_intro hs
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  janus_run [hz0, hz1, hz2, hz3]
  all_goals omega

end Fv256.Arm64.Log10
