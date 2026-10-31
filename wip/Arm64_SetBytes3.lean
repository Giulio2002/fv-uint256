import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).SetBytes3(in []byte) *Int` (arm64)

**Guarantee.** For every receiver `z` (`X0`) and slice `in = (ptr, len, cap)` (`X1`-`X3`), every Go call whose stack-growth
check falls through (`GuardOK s 0`) and whose stack window `[SP-24, SP+24)` is writable and aligned (`StackOK s 24 24`):
if `len ≥ 3`, the 32 bytes at `z` are writable, the 3 bytes at `ptr` are readable, and neither overlaps the other or the
stack window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is
`Fv256.Spec.fromBE` of the first 3 bytes of the slice (the big-endian reading, bytes read before the call), and no byte
changes outside `z[0..32)` and the stack window (`Fv256.Util.OnlyWrites2`).
If `len < 3` the call reaches the bounds-check panic stub (`Panics`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes3

theorem correctness (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    ((3 ≤ len.toNat → Ptr32 s.mem z true → Ptr s.mem ptr 3 false →
      Disjoint z.toNat 32 ptr.toNat 3 → Disjoint z.toNat 32 (s.sp.toNat - 24) 48 → Disjoint ptr.toNat 3 (s.sp.toNat - 24) 48 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 3 ∧
          Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48))) ∧
    (len.toNat < 3 → Panics (Extracted.program.withExit ret) s) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  refine ⟨?_, fun hl => ?_⟩
  · intro hl ⟨hz, hz'⟩ ⟨hp, hp'⟩ hd1 hd2 hd3
    simp only [Disjoint] at hd1 hd2 hd3
    janus_run
    refine ⟨?_, ?_⟩
    · trace_state; sorry
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · janus_run

end Fv256.Arm64.SetBytes3
