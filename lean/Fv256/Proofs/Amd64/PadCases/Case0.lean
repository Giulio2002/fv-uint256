import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Amd64.PadDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.PaddedBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem case0 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, 0#64]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        H [byteType, 0, 0] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 0 ∧ (s'.regs 1).toNat = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, ⟨hzw, hz⟩, hzo, hzd, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hzd ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x2b] calls [hmk]
  janus64_run
  refine ⟨_, rfl, ?_⟩
  janus_frame

end Fv256.Amd64.PaddedBytes
