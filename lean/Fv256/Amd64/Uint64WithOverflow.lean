import Extracted
import Fv256.Spec.Uint64WithOverflow
import Fv256.Spec.Uint64
import Fv256.Proofs.Amd64.Uint64WithOverflow

/-!
# amd64: the compiled `(*uint256.Int).Uint64WithOverflow` implements `Spec.uint64Ov`  (`Fv256/Spec/Uint64WithOverflow.lean`)

Go: `func (z *Int) Uint64WithOverflow() (uint64, bool)`. Calling it with the receiver `x` returns normally with `Fv256.Spec.uint64 x` in `RAX` and the overflow flag `Fv256.Spec.uint64Ov x` in the low byte of the second result register.
No fault and no panic occur. Memory is only read.
The tactic proof is `Fv256/Proofs/Amd64/Uint64WithOverflow.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Uint64WithOverflow

/-- PRECONDITION (machine facts only): the return-address slot is writable and the 32 bytes at `x` are readable (`Buffer`, from Janus). -/
def Pre (x : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s x 32 false

/-- POSTCONDITION: `RAX` is `Spec.uint64` of the number at `x` (its low 64 bits) and the low byte of `RBX` is `Spec.uint64Ov` of it (1 when it does not fit, else 0). -/
def Post (x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = Fv256.Spec.uint64 (valueAt s x 32) ∧
    (s'.regs 3).toNat % 256 = (Fv256.Spec.uint64Ov (valueAt s x 32)).toNat

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (Pre x) (Post x) :=
  correctness_proof x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and
`correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ Pre x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post x s s' :=
  Wit.nonvacuous

/-- EXACT RESULT on the concrete witness state: the call returns and the result is the expected literal. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ (s'.regs 0).toNat = 0 ∧ (s'.regs 3).toNat % 256 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.Uint64WithOverflow
