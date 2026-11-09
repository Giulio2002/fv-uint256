import Extracted
import Fv256.Spec.ISubUint64
import Fv256.Proofs.Amd64.ISubUint64

/-!
# amd64: the compiled `(*uint256.Int).ISubUint64` implements `Fv256.Spec.iSubU`  (`Fv256/Spec/ISubUint64.lean`)

Calling `z.ISubUint64(n)` with `z` in `RAX`, `n` in `RBX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.iSubU z n`, and changes no byte outside `z[0, 32)`.
The tactic proof is `Fv256/Proofs/Amd64/ISubUint64.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ISubUint64

/-- PRECONDITION (machine facts only): the return-address slot is writable (`StackWritable`); 32-byte buffers (`Buffer`):
`z` writable; `z` does not overlap the return-address slot. The scalar `n` (the 64-bit argument) needs no condition. -/
def Pre (z : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Disjoint z 32 (s.regs regSP) 8

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Fv256.Spec.iSubU z n` (numbers read BEFORE the call); only
`z[0, 32)` was written. -/
def Post (z n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.Spec.iSubU (valueAt s z 32) n.toNat ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n] (Pre z) (Post z n) :=
  correctness_proof z n

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (the witness call `z.ISubUint64(n)`) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧ Pre z s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z n s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.ISubUint64
