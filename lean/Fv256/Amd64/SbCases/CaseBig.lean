import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.SetBytesDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetBytes

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem caseBig (z ptr len cap : BitVec 64) (h32 : 32 ≤ len.toNat) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => StackGuardOK s 48 ∧ StackWritable s 88 24 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Buffer s z 32 true ∧ Buffer s ptr len.toNat false ∧
        (z.toNat + 32 ≤ ptr.toNat + len.toNat - used len.toNat ∨ ptr.toNat + len.toNat ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (ptr.toNat + len.toNat ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat + len.toNat - used len.toNat) ∧
        ((s.regs 14).toNat + 16 + 8 ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + len.toNat - used len.toNat + i) 1) (used len.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 88) 112) := by
    intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hd, hlc, hc48, ⟨hzw, hz⟩, ⟨hpw, hp⟩, hd1, hd2, hd3, hdg⟩
    janus64_intro hs
    have hgl := hg.load
    have hgb := hg.below
    have hnw2 := hg.noWrap
    have hgr := hg.readable
    simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hd2 hd3 hdg
    janus64_data hd [hacc]
    simp only [valueAt]
    have hu : used len.toNat = 32 := by simp [used]; omega
    rw [hu] at hd1 hd3 ⊢
    janus64_run [Util.readLE_32]
    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
         rw [show ptr.toNat + len.toNat - 32 = ptr.toNat + (len.toNat - 32) from by omega]
         rw [Util.be32_rev]
         rw [show ptr.toNat + (len.toNat - 32) + 24 = len.toNat + ptr.toNat - 8 from by omega,
           show ptr.toNat + (len.toNat - 32) + 16 = len.toNat + ptr.toNat - 16 from by omega,
           show ptr.toNat + (len.toNat - 32) + 8 = len.toNat + ptr.toNat - 24 from by omega,
           show ptr.toNat + (len.toNat - 32) = len.toNat + ptr.toNat - 32 from by omega]
         have h1 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 32) 8)
         have h2 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 24) 8)
         have h3 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 16) 8)
         have h4 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 8) 8)
         simp only [Nat.reducePow] at h1 h2 h3 h4
         omega)

end Fv256.Amd64.SetBytes
