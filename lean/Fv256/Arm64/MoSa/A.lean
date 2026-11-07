import Fv256.Arm64.MulOverflowProg
import Fv256.Spec
import Fv256.Util
import Fv256.UtilSa

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MoSa

set_option maxHeartbeats 64000000 in
theorem caseA (z x y : BitVec 64) :
    Ensures Fv256.Arm64.MulOverflowProg.program Fv256.Arm64.MulOverflowProg.entry [z, x, y]
      (fun s => GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Disjoint32 z.toNat x.toNat ∧ Disjoint32 z.toNat y.toNat ∧ Disjoint32 x.toNat y.toNat ∧ Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint y.toNat 32 (s.sp.toNat - 240) 256)
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        UtilSa.OnlyWrites3 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 232 (s.sp.toNat + 8) 8) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hd0, hd1, hd2, hd3, hd4, hd5⟩
  janus_intro hs
  simp only [Disjoint32, Disjoint] at *
  janus_run
  have := Util.readLE8_lt s.mem z.toNat
  have := Util.readLE8_lt s.mem (z.toNat + 8)
  have := Util.readLE8_lt s.mem (z.toNat + 16)
  have := Util.readLE8_lt s.mem (z.toNat + 24)
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  have := Util.readLE8_lt s.mem y.toNat
  have := Util.readLE8_lt s.mem (y.toNat + 8)
  have := Util.readLE8_lt s.mem (y.toNat + 16)
  have := Util.readLE8_lt s.mem (y.toNat + 24)
  refine ⟨?_, ?_, ?_⟩
  · refine Util.mo_flag _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · (simp only [Spec.W, Nat.reducePow]; janus_arith)
    · (simp only [Spec.W, Nat.reducePow]; janus_arith)
    · (simp only [Spec.W, Nat.reducePow]; janus_arith)
    · (simp only [Spec.W, Nat.reducePow]; janus_arith)
  · simp only [Spec.mul, Spec.W, Nat.reducePow]; janus_arith
  · simp (disch := omega) only [UtilSa.ow3_wl_iff, UtilSa.ow3_wq_iff, UtilSa.ow3_wr_iff, UtilSa.ow3_self_iff]

end Fv256.Arm64.MoSa
