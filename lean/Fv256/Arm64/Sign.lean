import Extracted
import Fv256.Spec.Sign
import Fv256.Proofs.Arm64.Sign

/-!
# arm64: the compiled `(*uint256.Int).Sign` implements `Spec.sign`  (`Fv256/Spec/Sign.lean`)

Go: `func (z *Int) Sign() int`. Calling it with the receiver `x` returns normally with `Fv256.Spec.sign x` (-1, 0, +1) in `X0`.
No fault and no panic occur. Memory is only read.
The tactic proof is `Fv256/Proofs/Arm64/Sign.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Sign

/-- PRECONDITION (machine facts only): the 32 bytes at `x` are readable (`Ptr32`, from Janus). -/
def Pre (x : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem x false

/-- POSTCONDITION: `X0`, read as a signed 64-bit integer, is `Spec.sign` of the number at `x` (-1, 0 or 1). -/
def Post (x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0) = BitVec.ofInt 64 (Fv256.Spec.sign (val256 s.mem x.toNat))

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
    ABIReturn Wit.s0 s' ∧ (s'.regs 0) = 0#64 :=
  Wit.returns

end Witness

end Fv256.Arm64.Sign
