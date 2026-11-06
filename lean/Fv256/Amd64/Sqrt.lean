import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.SqrtMath

/-!
# `(*uint256.Int).Sqrt(x *Int) *Int` (amd64): `z = ⌊√x⌋` (STUB statement; proof pending)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x200 ∧ 0x280 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1f0 0x20 ∧ s.xmm 15 = 0 ∧
    Buffer s z 32 true ∧ Buffer s x 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x20 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x20 ≤ x.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x20 ≤ (s.regs regG).toNat + 16)

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x)
      (fun s s' => s'.regs 0 = z ∧ Fv256.F.IsSqrt (valueAt s x 32) (valueAt s' z 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x1f0, (s.regs regSP).toNat + 0x20)]) := by
  sorry

end Fv256.Amd64.Sqrt
