import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.By1Loop

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.DivWork

namespace Fv256.Amd64.DivWork2

theorem by1_summary :
    Summary Extracted.program by1
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        StackGuardOK s 0 ∧ StackWritable s 16 40 ∧
        2 ≤ (s.regs 6).toNat ∧ (s.regs 6).toNat < 2 ^ 20 ∧ 2 ^ 63 ≤ (s.regs 9).toNat ∧
        (s.regs 6).toNat - 1 ≤ (s.regs 3).toNat ∧
        Buffer s (s.regs 0) (8 * ((s.regs 6).toNat - 1)) true ∧ Buffer s (s.regs 7) (8 * (s.regs 6).toNat) false ∧
        ((s.regs 0).toNat + 8 * ((s.regs 6).toNat - 1) ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 8 * (s.regs 6).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 0).toNat + 8 * ((s.regs 6).toNat - 1) ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 40 ≤ (s.regs 0).toNat) ∧
        ((s.regs 7).toNat + 8 * (s.regs 6).toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 40 ≤ (s.regs 7).toNat) ∧
        s.mem.readLE ((s.regs 7).toNat + 8 * ((s.regs 6).toNat - 1)) 8 < (s.regs 9).toNat)
      (fun s s' => True) := by
  intro s hpc ⟨⟨hra1, hra2⟩, hg, ⟨hlow, hnw, hacc⟩, hn1, hn2, hd1, hql, ⟨hqw, hq⟩, ⟨huw, hu⟩, hqu, hqs, hus, htop⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgr hgb hgl hnw2 hacc hlow hnw
  have hcode := by1Head_lt
  have hdivlt : ¬ (18446744073709551616 ≤ ((18446744073709551615 - BitVec.toNat (s.regs 9)) * 18446744073709551616 + 18446744073709551615) / BitVec.toNat (s.regs 9)) := by
    sorry
  janus64_run [BitVec.toNat_not, hdivlt] until [by1 + 0x49]
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.DivWork2
