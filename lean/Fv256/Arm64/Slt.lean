import Extracted
import Fv256.Spec.Slt
import Fv256.Proofs.Arm64.Slt

/-!
# arm64: the compiled `(*uint256.Int).Slt` implements `Spec.slt`  (`Fv256/Spec/Slt.lean`)

Go: `func (z *Int) Slt(x *Int) bool`. Calling it with the receiver `z` and the argument `x` returns normally with the boolean `Fv256.Spec.slt z x` in the low byte of `X0`.
No fault and no panic occur. Memory is only read.
The tactic proof is `Fv256/Proofs/Arm64/Slt.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Slt

/-- PRECONDITION (machine facts only): the 32 bytes at `z` and at `x` are readable (`Ptr32`, from Janus); `z` and `x` may be equal or overlap arbitrarily. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z false ∧ Ptr32 s.mem x false

/-- POSTCONDITION: the low byte of `X0` is `Spec.slt` of the number at `z` and the number at `x` (1 or 0), both read BEFORE the call. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat % 256 = (Fv256.Spec.slt (val256 s.mem z.toNat) (val256 s.mem x.toNat)).toNat

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

end Fv256.Arm64.Slt
