import Extracted
import Fv256.Spec.Cmp
import Fv256.Proofs.Amd64.Cmp

/-!
# amd64: the compiled `(*uint256.Int).Cmp` implements `Spec.cmp`  (`Fv256/Spec/Cmp.lean`)

Go: `func (z *Int) Cmp(x *Int) int`. Calling it with the receiver `z` and the argument `x` returns normally with the three-way comparison `Fv256.Spec.cmp z x` (-1, 0, +1) in `RAX`.
No fault and no panic occur. Memory is only read.
The tactic proof is `Fv256/Proofs/Amd64/Cmp.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Cmp

/-- PRECONDITION (machine facts only): the return-address slot is writable and the 32 bytes at `z` and at `x` are readable (`Buffer`, from Janus); `z` and `x` may be equal or overlap arbitrarily. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s x 32 false

/-- POSTCONDITION: `RAX`, read as a signed 64-bit integer, is `Spec.cmp` of the number at `z` and the number at `x` (-1, 0 or 1), both read BEFORE the call. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0) = BitVec.ofInt 64 (Fv256.Spec.cmp (valueAt s z 32) (valueAt s x 32))

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
    ABIReturn Wit.s0 s' ∧ (s'.regs 0) = 0#64 :=
  Wit.returns

end Witness

end Fv256.Amd64.Cmp
