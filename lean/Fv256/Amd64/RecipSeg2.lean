import Fv256.Amd64.RecipSeg1

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem seg2 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x14c)) (hs : RecPre s) (hq : RecQ1 s S)
    (Q : State → Prop) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1c1)) S Q := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨y3, y2, y1, y0, hr6, hr0, hr3, hr2, hr1, hr7, hr8, hr9, hy2, hy1, hy0, hs24, hs32, hs40, hs48, hregs, hmem, h63, hlt⟩ := hq
  obtain ⟨hr4, hr5, hr14, hx⟩ := hregs
  have hfr := hmem.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [Util.readLE_32, hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hsp4]
  all_goals (trace_state; sorry)

end Fv256.Amd64.RecipSeg
