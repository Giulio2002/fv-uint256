import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.SetBytesDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem caseBig (z ptr len cap : BitVec 64) (h32 : 32 ≤ len.toNat) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => GuardOK s 48 ∧ StackOK s 88 72 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr len.toNat false ∧
        Disjoint z.toNat 32 (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) ∧
        Disjoint z.toNat 32 (s.sp.toNat - 88) 160 ∧
        Disjoint (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) (s.sp.toNat - 88) 160 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 160)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + len.toNat - used len.toNat + i) 1) (used len.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 88) 160) := by
    intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hz, hz'⟩, ⟨hp, hp'⟩, hd1, hd2, hd3, hdg⟩
    janus_intro hs
    janus_data hd [hw]
    simp only [Disjoint] at hdg
    simp only [Disjoint, used, if_neg (show ¬ len.toNat < 32 by omega)] at hd1 hd2 hd3 ⊢
    janus_run
    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
         rw [show ptr.toNat + len.toNat - 32 = ptr.toNat + (len.toNat - 32) from by omega]
         rw [Util.be32_rev]
         rw [Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _)]
         omega)

end Fv256.Arm64.SetBytes
