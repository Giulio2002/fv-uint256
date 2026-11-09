import Extracted
import Fv256.Spec.SubOverflow
import Fv256.Spec.Sub
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.SubOverflow

/-!
# amd64: the compiled `(*uint256.Int).SubOverflow` implements `Fv256.Spec.subOv`  (`Fv256/Spec/SubOverflow.lean`)

Calling `z.SubOverflow(x, y)` with `z` in `RAX`, `x` in `RBX`, `y` in `RCX` returns normally (no fault, no panic) with `RAX = z`, returns in the low byte of `RBX` the flag `Fv256.Spec.subOv x y`, leaves in `z` the number
`Fv256.Spec.sub x y`, and changes no byte outside `z[0, 32)`. `z`, `x`, `y` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/SubOverflow.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.SubOverflow

/-- PRECONDITION (machine facts only): the return-address slot is writable (`StackWritable`); 32-byte buffers (`Buffer`):
`z` writable, `x`, `y` readable; `z` does not overlap the return-address slot; `z`, `x`, `y` are pairwise equal-or-
disjoint (`Alias32`). -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 0 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧ Alias32 z x ∧ Alias32 z y ∧
  Alias32 x y

/-- POSTCONDITION: `RAX = z`; the low byte of `RBX` is `Fv256.Spec.subOv x y`; the number now at `z` is
`Fv256.Spec.sub x y` (numbers read BEFORE the call); only `z[0, 32)` was written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ (s'.regs 3).toNat % 256 = (Fv256.Spec.subOv (valueAt s x 32) (valueAt s y 32)).toNat ∧
  valueAt s' z 32 = Fv256.Spec.sub (valueAt s x 32) (valueAt s y 32) ∧ Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (the witness call `z.SubOverflow(x, y)`) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.SubOverflow
