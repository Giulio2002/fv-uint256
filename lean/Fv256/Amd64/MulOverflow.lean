import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.MoCases.A
import Fv256.Amd64.MoCases.B
import Fv256.Amd64.MoCases.C
import Fv256.Amd64.MoCases.D
import Fv256.Amd64.MoCases.E

/-!
# `(*uint256.Int).MulOverflow(x, y *Int) (*Int, bool)` (amd64): `z = x * y mod 2^256` and the overflow flag

**Guarantee.** For all pointers `z`, `x`, `y` (`RAX`, `RBX`, `RCX`) with the 32 bytes at `z` writable and those at `x`, `y` readable (below `2^48`),
every pair of the three pointers equal or disjoint, the 168-byte window around the stack pointer (`StackWritable s 152 16`: the function's frame and
the extracted `umul` callee's) disjoint from the three objects, `RSP` 8-aligned, and a Go call whose stack check falls through (`StackGuardOK s 0`):
the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the overflow flag in `RBX` (low byte) is `1` iff `x*y >= 2^256`, the number at `z`
afterwards is `Fv256.Spec.mul` of the numbers at `x` and `y` before the call, and no byte changes outside `z[0..32)` and the stack window.
One proof module per aliasing pattern of `(z, x, y)` (`MoCases/A..E`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulOverflow

def Alias (p q : BitVec 64) : Prop := p = q ∨ p.toNat + 32 ≤ q.toNat ∨ q.toNat + 32 ≤ p.toNat

set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ (s.regs regSP).toNat % 8 = 0 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Alias z x ∧ Alias z y ∧ Alias x y ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ y.toNat))
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 3).toNat % 256 = (if Spec.W ≤ valueAt s x 32 * valueAt s y 32 then 1 else 0) ∧
        valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 152) 168) := by
  intro ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩
  rcases hzx with hzx | hzx
  · subst hzx
    rcases hzy with hzy | hzy
    · subst hzy
      exact caseE _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hd1⟩
    · exact caseB _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzy, hd1, hd3⟩
  · rcases hzy with hzy | hzy
    · subst hzy
      exact caseC _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hd1, hd2⟩
    · rcases hxy with hxy | hxy
      · subst hxy
        exact caseD _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hd1, hd2⟩
      · exact caseA _ _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩

-- Witness: to be added once the cases verify (state as in Clone/amd64: guard register, stack window, wmem64-style memory).

end Fv256.Amd64.MulOverflow
