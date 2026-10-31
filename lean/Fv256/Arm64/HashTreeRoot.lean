import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).HashTreeRoot() ([32]byte, error)` (arm64)

**Guarantee.** For every receiver `z` (`X0`) with 32 readable bytes, a Go call whose stack window `[SP-88, SP+40)` is writable and
aligned (`StackOK s 88 40`) and does not overlap `z`, and the Go frame-pointer convention: the call returns, obeys the ABI, the 32 result
bytes at `SP+8` (the caller's frame) read as the little-endian number equal to the number at `z` (the SSZ encoding of a `uint256`), the
returned `error` is `nil` (`X0 = X1 = 0`), and no byte changes outside the result and the frame.

**Non-vacuity.** `Witness.nonvacuous` / `Witness.returns`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.HashTreeRoot

theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => Ptr32 s.mem z false ∧ StackOK s 88 40 ∧ Disjoint z.toNat 32 (s.sp.toNat - 88) 128 ∧ s.regs 29 = s.sp - 8#64)
      (fun s s' => s'.mem.readLE (s.sp.toNat + 8) 32 = val256 s.mem z.toNat ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
        Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 88) 88) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hal, hb, ha, hw⟩, hdis, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run
  trace_state
  all_goals fail "x"

end Fv256.Arm64.HashTreeRoot
