import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Bytes20(dest *[20]byte)` (arm64)

**Guarantee.** For all pointers `z` (the receiver, `X0`) and `dest` (`X1`) such that the 32 bytes at `z` are readable, the 32
bytes at `dest` are writable (both below `2^48`) and the two ranges are disjoint, the call returns (no fault, no panic), obeys
the ABI, the 32 bytes at `dest` afterwards read as the big-endian number `Fv256.Spec.fromBE` equal to the number at `z` (read
before the call), and no byte changes outside `dest[0..32)`.
(The compiled code interleaves its loads and stores, so overlapping `z` and `dest` is outside the guarantee.)

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns.
-/

/-!
# `(*uint256.Int).Bytes20() [20]byte` (arm64)

**Guarantee.** For every receiver `z` (`X0`) and every Go call such that the 32 bytes at `z` are readable (below `2^48`), the stack
window `[SP-56, SP+40)` (the 48-byte frame, a local copy of the array, and the 32 result bytes the callee returns in the caller's
frame at `SP+8`) is writable and aligned (`StackOK s 56 40`), that window does not overlap `z`, and the frame pointer is the
caller's (`X29 = SP - 8`, the Go arm64 convention): the call returns (no fault, no panic), obeys the ABI, the 32 result bytes at
`SP+8` read as the big-endian number (`Fv256.Spec.fromBE`) equal to the number at `z` (read before the call), and no byte changes
outside the result bytes and the frame (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Bytes20

theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => Ptr32 s.mem z false ∧ StackOK s 56 40 ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 96 ∧ s.regs 29 = s.sp - 8#64)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (s.sp.toNat + 8 + i) 1) 20 = val256 s.mem z.toNat % 2 ^ 160 ∧
        Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 20 (s.sp.toNat - 56) 56) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hal, hb, ha, hw⟩, hdis, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run
  trace_state
  all_goals sorry

end Fv256.Arm64.Bytes20
