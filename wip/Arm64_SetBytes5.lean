import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).SetBytes5(in []byte) *Int` (arm64)

**Guarantee.** For every receiver `z` (`X0`) and slice `in = (ptr, len, cap)` (`X1`-`X3`), every Go call whose stack-growth
check falls through (`GuardOK s 0`) and whose stack window `[SP-24, SP+24)` is writable and aligned (`StackOK s 24 24`):
if `len ≥ 5`, the 32 bytes at `z` are writable, the 5 bytes at `ptr` are readable, and neither overlaps the other or the
stack window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is
`Fv256.Spec.fromBE` of the first 5 bytes of the slice (the big-endian reading, bytes read before the call), and no byte
changes outside `z[0..32)` and the stack window (`Fv256.Util.OnlyWrites2`).
If `len < 5` the call reaches the bounds-check panic stub (`Panics`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes5

theorem correctness (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    ((5 ≤ len.toNat → Ptr32 s.mem z true → Ptr s.mem ptr 5 false →
      Disjoint z.toNat 32 ptr.toNat 5 → Disjoint z.toNat 32 (s.sp.toNat - 24) 48 → Disjoint ptr.toNat 5 (s.sp.toNat - 24) 48 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 5 ∧
          Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48))) ∧
    (len.toNat < 5 → Panics (Extracted.program.withExit ret) s) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  refine ⟨?_, fun hl => ?_⟩
  · intro hl ⟨hz, hz'⟩ ⟨hp, hp'⟩ hd1 hd2 hd3
    simp only [Disjoint] at hd1 hd2 hd3
    janus_run
    refine ⟨?_, ?_⟩
    · have := Util.rd1_lt s.mem ptr.toNat; have := Util.rd1_lt s.mem (ptr.toNat + 1); have := Util.rd1_lt s.mem (ptr.toNat + 2); have := Util.rd1_lt s.mem (ptr.toNat + 3); have := Util.rd1_lt s.mem (ptr.toNat + 4); simp only [Util.chunk8, Util.chunk4, Util.chunk2]; simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Nat.mod_eq_of_lt]; omega
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · janus_run

end Fv256.Arm64.SetBytes5
