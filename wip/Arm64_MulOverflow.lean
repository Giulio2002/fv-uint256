import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulOverflow

set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s)
    (hg : GuardOK s 0) (hst : StackOK s 240 16) :
    (Ptr32 s.mem z true → Ptr32 s.mem x false → Ptr32 s.mem y false →
      Aliasing z x → Aliasing z y → Aliasing x y →
      Disjoint z.toNat 32 (s.sp.toNat - 240) 256 → Disjoint x.toNat 32 (s.sp.toNat - 240) 256 →
      Disjoint y.toNat 32 (s.sp.toNat - 240) 256 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
          Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 256)) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  intro ⟨hz, hz'⟩ ⟨hx, hx'⟩ ⟨hy, hy'⟩ hzx hzy hxy hd1 hd2 hd3
  rcases hzx with rfl | hzx
  · sorry
  rcases hzy with rfl | hzy
  · sorry
  rcases hxy with rfl | hxy
  · sorry
  simp only [Disjoint] at *
  janus_run
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
    all_goals (simp only [Spec.W, Nat.reducePow]; janus_arith)
  · sorry
  · sorry

end Fv256.Arm64.MulOverflow
