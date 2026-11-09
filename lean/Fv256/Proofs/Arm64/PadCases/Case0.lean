import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.PadDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.PaddedBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem case0 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, 0#64]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [byteType, 0, 0] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = 0 ∧ (s'.regs 2).toNat = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, ⟨hz, hz'⟩, hzo, hzd, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hzd
  janus_run until [Extracted.entry + 0x30] calls [hmk]
  janus_run
  refine ⟨_, rfl, ?_⟩
  janus_frame

end Fv256.Arm64.PaddedBytes
