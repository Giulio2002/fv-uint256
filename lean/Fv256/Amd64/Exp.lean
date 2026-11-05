import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.ExpMath
import Fv256.UtilF
import Fv256.Amd64.ExpSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Exp

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage1 (z b e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b, e]
      (fun s => StackGuardOK s 0x20 ∧ 0x100 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xa8 0x20 ∧ Extracted.program.DataLoaded s.mem ∧
        Buffer s z 32 true ∧ Buffer s b 32 false ∧ Buffer s e 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ z.toNat) ∧
        (b.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ b.toNat) ∧
        (e.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ e.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ (s.regs regG).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧ True) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, hd, ⟨hzw, hz⟩, ⟨hbw, hb⟩, ⟨hew, he⟩, hdz, hdb, hde, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdb hde hsp
  janus64_data hd [hacc]
  janus64_run [Util.readLE_32] until [Extracted.entry + 0x149]
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.Exp
