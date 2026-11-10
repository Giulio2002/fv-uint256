import Extracted
import Fv256.Spec.IsZero
import Fv256.Proofs.Amd64.IsZero

/-!
# amd64: the compiled `(*uint256.Int).IsZero` implements `Spec.isZero`  (`Fv256/Spec/IsZero.lean`)

Go: `func (z *Int) IsZero() bool`. Calling it with the receiver `x` returns normally with the boolean `Fv256.Spec.isZero x` in the low byte of `RAX`.
No fault and no panic occur. Memory is only read.
The tactic proof is `Fv256/Proofs/Amd64/IsZero.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

namespace Fv256.Amd64.IsZero

/-- PRECONDITION (machine facts only): the return-address slot is writable and the 32 bytes at `x` are readable (`Buffer`, from Janus). -/
def Pre (x : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s x 32 false

/-- POSTCONDITION: the low byte of `RAX` is `Spec.isZero` of the number at `x` (1 or 0). -/
def Post (x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat % 256 = (Fv256.Spec.isZero (valueAt s x 32)).toNat

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
    ABIReturn Wit.s0 s' ∧ (s'.regs 0).toNat % 256 = 1 :=
  Wit.returns

end Witness

end Fv256.Amd64.IsZero
