import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD
import Fv256.Arm64.Float64Lsh

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

set_option profiler true in
set_option profiler.threshold 3000 in
set_option maxHeartbeats 80000000 in
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0)
      (fun s s' => s'.getV 0 64 = Fv256.B.float64BitsNearest (val256 s.mem x.toNat) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨hx, hx'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdis, hf⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run calls [hS := Fv256.Arm64.Float64.lsh_summary (s.sp - 40#64) x]
  all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat] at *)
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  all_goals sorry

end Fv256.Arm64.Float64
