import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.HexLemmas
import Fv256.HexSpec

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Fv256.C Fv256.Hex

namespace Fv256.Amd64.Hex

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4208 8 ∧ Extracted.program.DataLoaded s.mem ∧ s.xmm 15 = 0 ∧
        Outside ((s.regs 4).toNat - 4208) 4216 rt ∧ Outside 5142664 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (∀ n, 1 ≤ n → n ≤ 64 → H [0, (s.regs 4).toNat - 112 + 38 + (64 - n), n + 2]
          (s.regs 14).toNat ((s.regs 4).toNat - 112) (rtView rt s.mem)))
      (fun s s' => HexOut (valueAt s z 32) s'.mem (s'.regs 0).toNat (s'.regs 3).toNat ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hw, hd, hx15, hout, hout2, hal, ⟨hzn, hza⟩, hzd, hgd, hH⟩
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  janus64_run until [Extracted.entry + 0xec]
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.Hex
