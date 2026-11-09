import Extracted
import Fv256.Spec.IAdd
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.IAdd

/-!
# amd64: the compiled `(*uint256.Int).IAdd` implements `Fv256.Spec.iAdd`  (`Fv256/Spec/IAdd.lean`)

Calling `z.IAdd(x)` with `z` in `RAX`, `x` in `RBX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.iAdd z x`, and changes no byte outside `z[0, 32)`. `z` and `x` may be the same object but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/IAdd.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.IAdd

/-- PRECONDITION (machine facts only): the return-address slot is writable (`StackWritable`); 32-byte buffers (`Buffer`):
`z` writable, `x` readable; `z` does not overlap the return-address slot; `z` and `x` are equal-or-disjoint
(`Alias32`). -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Disjoint z 32 (s.regs regSP) 8 ∧ Alias32 z x

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Fv256.Spec.iAdd z x` (numbers read BEFORE the call); only
`z[0, 32)` was written. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.Spec.iAdd (valueAt s z 32) (valueAt s x 32) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (the witness call `z.IAdd(x)`) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.IAdd
