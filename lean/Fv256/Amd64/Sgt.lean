import Extracted
import Fv256.Spec.Sgt
import Fv256.Proofs.Amd64.Sgt

/-!
# amd64: the compiled `(*uint256.Int).Sgt` implements `Spec.sgt`  (`Fv256/Spec/Sgt.lean`)

Go: `func (z *Int) Sgt(x *Int) bool`. Calling it with the receiver `z` and the argument `x` returns normally with the boolean `Fv256.Spec.sgt z x` in the low byte of `RAX`.
No fault and no panic occur. Memory is only read.
The tactic proof is `Fv256/Proofs/Amd64/Sgt.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sgt

/-- PRECONDITION (machine facts only): the return-address slot is writable and the 32 bytes at `z` and at `x` are readable (`Buffer`, from Janus); `z` and `x` may be equal or overlap arbitrarily. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s x 32 false

/-- POSTCONDITION: the low byte of `RAX` is `Spec.sgt` of the number at `z` and the number at `x` (1 or 0), both read BEFORE the call. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat % 256 = (Fv256.Spec.sgt (valueAt s z 32) (valueAt s x 32)).toNat

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and
`correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

/-- EXACT RESULT on the concrete witness state: the call returns and the result is the expected literal. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ (s'.regs 0).toNat % 256 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.Sgt
