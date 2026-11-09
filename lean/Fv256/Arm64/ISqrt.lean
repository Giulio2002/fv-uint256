import Extracted
import Fv256.Spec.ISqrt
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.ISqrt

/-!
# arm64: the compiled `(*uint256.Int).ISqrt` implements `Fv256.Spec.IsSqrt`  (`Fv256/Spec/ISqrt.lean`)

Calling `z.ISqrt()` with `z` in `X0` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` a number `r` with
`Fv256.Spec.IsSqrt (old z) r`, and writes only `z[0, 32)` and its own stack frame.
The tactic proof is `Fv256/Proofs/Arm64/ISqrt.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ISqrt

/-- PRECONDITION (machine facts only): the stack-growth check falls through with room for the large frame (`GuardOK`, `StackOK`, `520 ≤ SP`); the goroutine's `stackguard0` word
(at `X28 + 16`) is outside the frame; `z` is a writable 32-byte buffer (`Ptr32`) disjoint from the frame `[SP-520, SP+8)`. -/
def Pre (z : BitVec 64) (s : State) : Prop :=
  GuardOK s 480 ∧ StackOK s 520 8 ∧ 520 ≤ s.sp.toNat ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 520 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 520) 528

/-- POSTCONDITION: `X0 = z`; the number now at `z` is the integer square root (`Spec.IsSqrt`) of the number at `z` BEFORE the call; memory changed only in
`z[0, 32)` and the frame `[SP-520, SP)`. -/
def Post (z : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ Fv256.Spec.IsSqrt (val256 s.mem z.toNat) (val256 s'.mem z.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 520, s.sp.toNat)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z] (Pre z) (Post z) :=
  correctness_proof z

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.ISqrt()`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ Pre z s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.ISqrt
