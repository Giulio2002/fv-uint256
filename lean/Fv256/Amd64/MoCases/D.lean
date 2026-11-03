import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulOverflow

set_option exponentiation.threshold 600 in
set_option maxHeartbeats 64000000 in
theorem caseD (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ (s.regs regSP).toNat % 8 = 0 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s x 32 false ∧ ((z.toNat + 32 ≤ x.toNat) ∨ (x.toNat + 32 ≤ z.toNat)) ∧ (z.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧ (x.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat))
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 3).toNat % 256 = (if Spec.W ≤ valueAt s x 32 * valueAt s x 32 then 1 else 0) ∧
        valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s x 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 152) 168) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hal, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hd0, hd1, hd2⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hal hd0 hd1 hd2
  simp only [valueAt]
  janus64_run
  have := Util.readLE8_lt s.mem z.toNat
  have := Util.readLE8_lt s.mem (z.toNat + 8)
  have := Util.readLE8_lt s.mem (z.toNat + 16)
  have := Util.readLE8_lt s.mem (z.toNat + 24)
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  have hvx : Janus.Arm64.Memory.readLE s.mem x.toNat 32 < 2 ^ 256 := by
    simpa [Nat.reducePow] using Janus.Arm64.Memory.readLE_lt s.mem x.toNat 32
  all_goals (simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_mod])
  refine Util.mo_flag8 _ _ _ _ _ _ hvx hvx ?_ ?_ ?_ ?_
  · (simp only [Util.readLE_32, Spec.W, Nat.reducePow]; janus_carry)
  · (simp only [Util.readLE_32, Spec.W, Nat.reducePow]; janus_carry)
  · (simp only [Util.readLE_32, Spec.W, Nat.reducePow]; janus_carry)
  · (simp only [Util.readLE_32, Spec.W, Nat.reducePow]; janus_carry)

end Fv256.Amd64.MulOverflow
