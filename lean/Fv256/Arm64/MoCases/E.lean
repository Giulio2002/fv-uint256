import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulOverflow

set_option maxHeartbeats 64000000 in
theorem caseE (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, z, z]
      (fun s => GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem z false ∧ Ptr32 s.mem z false ∧ Disjoint z.toNat 32 (s.sp.toNat - 240) 256)
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem z.toNat * val256 s.mem z.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem z.toNat) (val256 s.mem z.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 256) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hd0⟩
  janus_intro hs
  simp only [Disjoint32, Disjoint] at *
  janus_run
  have := Util.readLE8_lt s.mem z.toNat
  have := Util.readLE8_lt s.mem (z.toNat + 8)
  have := Util.readLE8_lt s.mem (z.toNat + 16)
  have := Util.readLE8_lt s.mem (z.toNat + 24)
  refine ⟨?_, ?_, ?_⟩
  · refine Util.mo_flag _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ <;> first | omega | (simp only [Spec.W, Nat.reducePow]; janus_arith)
  · simp only [Spec.mul, Spec.W, Nat.reducePow]; janus_arith
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

end Fv256.Arm64.MulOverflow
