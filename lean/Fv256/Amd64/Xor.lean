import Extracted
import Fv256.Spec.Xor
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Xor

/-!
# amd64: the compiled `(*uint256.Int).Xor` implements `Fv256.Spec.xor`  (`Fv256/Spec/Xor.lean`)

Calling `z.Xor(x, y)` with `z` in `RAX`, `x` in `RBX`, `y` in `RCX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.xor x y`, and changes no byte outside `z[0, 32)`. `z`, `x`, `y` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/Xor.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Xor

/-- PRECONDITION (machine facts only): the return-address slot is writable (`StackWritable`); 32-byte buffers (`Buffer`):
`z` writable, `x`, `y` readable; `z` does not overlap the return-address slot; `z`, `x`, `y` are pairwise equal-or-
disjoint (`Alias32`). -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
  Disjoint z 32 (s.regs regSP) 8 ∧ Alias32 z x ∧ Alias32 z y ∧ Alias32 x y

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Fv256.Spec.xor x y` (numbers read BEFORE the call); only
`z[0, 32)` was written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.Spec.xor (valueAt s x 32) (valueAt s y 32) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (the witness call `z.Xor(x, y)`) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.Xor
