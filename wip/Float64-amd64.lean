import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Float64

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s)
      (fun s s' => (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64Bits (valueAt s x 32) ∧
        Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat - 80) 88 ((s.regs regSP).toNat - 80) 88) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hxw, hx⟩, hds, hm⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  simp only [regSP] at hacc hlow hnw hds
  simp only [valueAt]
  by_cases h3 : s.mem.readLE (x.toNat + 24) 8 = 0
  · by_cases h2 : s.mem.readLE (x.toNat + 16) 8 = 0
    · by_cases h1 : s.mem.readLE (x.toNat + 8) 8 = 0
      · sorry
      · sorry
    · sorry
  · janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, Nat.or_eq_zero_iff, h3]
    all_goals trace_state
    all_goals sorry

end Fv256.Amd64.Float64
