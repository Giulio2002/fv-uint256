import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.SqrtMath
import Fv256.SqrtHead
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.SqrtBig

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem probe_big :
    Summary Extracted.program Extracted.entry
      (fun s => SPre s ∧ (s.mem.readLE ((s.regs 3).toNat + 8) 8 ≠ 0 ∨ s.mem.readLE ((s.regs 3).toNat + 16) 8 ≠ 0 ∨
        s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0))
      SPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hzx, hdg⟩, hbig⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  have hor : ¬ (s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧
        s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  janus64_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor] until [Extracted.entry + 0x205]
    calls [Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshSumA.lsh_summary_alias (s.regs 4 - 40#64)),
           Fv256.CodeIn.lib_summary hcRsh (Fv256.Amd64.RshSum.rsh_summary (s.regs 4 - 72#64) (s.regs 3))]
  trace_state
  all_goals sorry

end Fv256.Amd64.Sqrt
