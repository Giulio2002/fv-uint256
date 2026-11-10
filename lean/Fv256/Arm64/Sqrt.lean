import Extracted
import Fv256.Spec.Sqrt
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.Sqrt

/-!
# arm64: the compiled `(*uint256.Int).Sqrt` implements `Fv256.Spec.IsSqrt`  (`Fv256/Spec/Sqrt.lean`)

Calling `z.Sqrt(x)` with `z, x` in `X0, X1` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` a number `r` with
`Fv256.Spec.IsSqrt x r` (the integer square root), and writes only `z[0, 32)` and its own stack frame.
The tactic proof is `Fv256/Proofs/Arm64/Sqrt.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Sqrt

/-- PRECONDITION (machine facts only): the stack-growth check falls through with room for the large frame (`GuardOK`, `StackOK`, `488 ≤ SP`); the goroutine's `stackguard0` word
(at `X28 + 16`) is outside the frame; `z` is a writable and `x` a readable 32-byte buffer (`Ptr32`), both disjoint from the frame
`[SP-488, SP+24)`. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  GuardOK s 448 ∧ StackOK s 488 24 ∧ 488 ≤ s.sp.toNat ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧
  Disjoint z.toNat 32 (s.sp.toNat - 488) 512 ∧ Disjoint x.toNat 32 (s.sp.toNat - 488) 512

/-- POSTCONDITION: `X0 = z`; the number now at `z` is the integer square root (`Spec.IsSqrt`) of the number at `x` BEFORE the call; memory changed only in
`z[0, 32)` and the frame `[SP-488, SP+24)`. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ Fv256.Spec.IsSqrt (val256 s.mem x.toNat) (val256 s'.mem z.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 488, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Sqrt(x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.Sqrt
